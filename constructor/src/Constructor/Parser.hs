{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Grammar functions written generically against any annotation regime
--   via 'HasAnn'.  Threads two pieces of context explicitly:
--
--   * Current 'Path' — the position in the AST, used to give each
--     '∀l.' binder a deterministic identity derived from its source
--     position rather than a per-parse counter.
--   * Binder map 'Map Name Path' — names of currently-bound level
--     variables and their introducing paths.  Inside @*l@ or
--     @*(l + n)@, looking up @l@ yields the path that becomes the
--     'LVar' identity.
module Constructor.Parser
  ( parseProgram
  , program
  , Parser
  , RawTree
  ) where

import Constructor.AST (Tree)
import Constructor.Path (Path, PathStep (..), emptyPath, extendPath)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (HasAnn (..), Lang (..), Name)
import Control.Monad (foldM, void)
import Data.Char (isAlpha, isAlphaNum)
import Data.Functor.Const (Const (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text
type RawTree s = Tree (Const ()) s

-- | Binders threaded through the grammar — three disjoint surface-name
--   namespaces: level-variable binders (from @∀l.@), type-parameter
--   binders (from @data Foo a@), and type-constructor binders (from
--   @data Foo … @).
data Binders = Binders
  { lvBinders :: !(Map Name Path)
    -- ^ '∀l.'-bound names → their binder path.
  , tyBinders :: !(Map Name Path)
    -- ^ Data-type-parameter names → their parameter-binding path.
  , tcBinders :: !(Map Name Path)
    -- ^ Type-constructor names → their data-declaration path.
  }

emptyBinders :: Binders
emptyBinders = Binders Map.empty Map.empty Map.empty

extendLv :: Name -> Path -> Binders -> Binders
extendLv n p b = b { lvBinders = Map.insert n p (lvBinders b) }

extendTys :: [(Name, Path)] -> Binders -> Binders
extendTys ps b = b { tyBinders = foldr (\(n, p) -> Map.insert n p) (tyBinders b) ps }

extendTc :: Name -> Path -> Binders -> Binders
extendTc n p b = b { tcBinders = Map.insert n p (tcBinders b) }

-- Whitespace + line/block comments.
sc :: (MonadParsec Void Text m) => m ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: (MonadParsec Void Text m) => m a -> m a
lexeme = L.lexeme sc

symbol :: (MonadParsec Void Text m) => Text -> m Text
symbol = L.symbol sc

keywords :: [Text]
keywords = ["data", "forall"]

identifier :: (MonadParsec Void Text m, MonadFail m) => m Name
identifier = lexeme . try $ do
  s <- (:) <$> satisfy isAlpha <*> many (satisfy isAlphaNumOrUnder)
  let t = T.pack s
  if t `elem` keywords
    then fail ("keyword " <> show s <> " used as identifier")
    else pure t
  where
    isAlphaNumOrUnder c = isAlphaNum c || c == '_' || c == '\''

-- | Parse a list of grammar elements separated by @sep@, threading
--   an accumulator from each element to the next so that later
--   siblings see binders introduced by earlier ones (in particular,
--   each @data X@ declaration adds @X@ to the type-constructor
--   namespace before subsequent siblings are parsed).  Each element
--   is given its sibling index for path construction.
sepEndByIndexedAcc
  :: MonadParsec e s mm => (Int -> acc -> mm (a, acc)) -> mm b -> acc -> mm ([a], acc)
sepEndByIndexedAcc mk sep = go 0
  where
    go i acc = do
      mx <- optional (try (mk i acc))
      case mx of
        Nothing       -> pure ([], acc)
        Just (x, acc') -> do
          msep <- optional sep
          case msep of
            Nothing -> pure ([x], acc')
            Just _  -> do
              (xs, acc'') <- go (i + 1) acc'
              pure (x : xs, acc'')

-- ----------------------------------------------------------------------
-- Expression-level parsers.
-- ----------------------------------------------------------------------

-- | Universe expression starting with @*@.
universe
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> Binders -> m (r a 'SExpr)
universe _path binders = lexeme $ do
  void (char '*')
  choice
    [ try $ do
        n   <- L.decimal
        ann <- freshExprAnn
        pure (star ann n)
    , between (symbol "(") (symbol ")") $ do
        n <- identifier
        case Map.lookup n (lvBinders binders) of
          Just binderPath -> do
            offset <- option 0 (symbol "+" *> L.decimal)
            ann    <- freshExprAnn
            pure (starVar ann n binderPath offset)
          Nothing -> fail ("unbound level variable: " <> T.unpack n)
    , do
        n <- identifier
        case Map.lookup n (lvBinders binders) of
          Just binderPath -> do
            ann <- freshExprAnn
            pure (starVar ann n binderPath 0)
          Nothing -> fail ("unbound level variable: " <> T.unpack n)
    ]

atom
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> Binders -> m (r a 'SExpr)
atom path binders = choice
  [ universe path binders
  , do
      n <- identifier
      -- Resolution order: type parameters shadow tycons in scope; an
      -- unresolved name falls through to 'var' so the elaborator can
      -- still surface 'TyUnbound'.
      case Map.lookup n (tyBinders binders) of
        Just paramPath -> do
          ann <- freshExprAnn
          pure (tyParamRef ann n paramPath)
        Nothing -> case Map.lookup n (tcBinders binders) of
          Just declPath -> do
            ann <- freshExprAnn
            pure (tyConRef ann n declPath)
          Nothing -> do
            ann <- freshExprAnn
            pure (var ann n)
  , between (symbol "(") (symbol ")") (expr (extendPath PsParens path) binders)
  ]

-- | @∀l. expr@ — level-binder introduction.  The binder's 'Path' is
--   the *current* path (where the @∀@ sits); the body is parsed at
--   @path ++ [PsForallBody]@ with the binder added to scope.
forallExpr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> Binders -> m (r a 'SExpr)
forallExpr path binders = do
  void (symbol "\8704" <|> symbol "forall")
  n <- identifier
  void (symbol ".")
  let binderPath = path
      binders'   = extendLv n binderPath binders
  body <- expr (extendPath PsForallBody path) binders'
  ann  <- freshExprAnn
  pure (forallLv ann n binderPath body)

expr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> Binders -> m (r a 'SExpr)
expr path binders = forallExpr path binders <|> arrowExpr path binders

arrowExpr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> Binders -> m (r a 'SExpr)
arrowExpr path binders = do
  a <- application (extendPath PsArrL path) binders
  option a $ do
    void (symbol "->")
    b   <- expr (extendPath PsArrR path) binders
    ann <- freshExprAnn
    pure (arr ann a b)

-- | Left-associative juxtaposition for type-level application:
--   @f x y z@ parses to @app (app (app f x) y) z@.
application
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> Binders -> m (r a 'SExpr)
application path binders = do
  head_ <- atom path binders
  args  <- many (atom path binders)
  foldM apply1 head_ args
  where
    apply1 f x = do
      ann <- freshExprAnn
      pure (app ann f x)

-- ----------------------------------------------------------------------
-- Declaration-level parsers.
-- ----------------------------------------------------------------------

-- | Parse one declaration.  Returns the parsed value along with the
--   updated 'Binders' that subsequent siblings should see — in
--   particular, 'dataD' adds itself to 'tcBinders' so that following
--   constructor types and data declarations can reference it.
decl
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> Binders -> m (r a 'SDecl, Binders)
decl path binders = dataD <|> ctorD
  where
    dataD = do
      void (symbol "data")
      n      <- identifier
      params <- many identifier  -- zero-or-more parameter names
      void (symbol ":")
      e   <- expr (extendPath PsDataAnn path) binders
      -- Inside the data body, the outer ∀-scope does NOT carry over,
      -- but: the data's own type parameters DO (scoped over each
      -- constructor's type), the data binder itself DOES (so
      -- constructors can mention the type they construct, and so
      -- nested data can reference it), and the outer tcBinders DO
      -- (top-level tycons remain visible inside nested bodies).
      let paramPaths   = zipWith (\i p -> (p, extendPath (PsDataParam i) path))
                                 [0 ..] params
          bodyBinders0 = binders { lvBinders = Map.empty }
          bodyBinders  = extendTc n path (extendTys paramPaths bodyBinders0)
      (ds, _)  <- between (symbol "{") (symbol "}") $
                    sepEndByIndexedAcc
                      (\i bs -> decl (extendPath (PsDeclIdx i) path) bs)
                      (symbol ";")
                      bodyBinders
      ann <- freshDeclAnn
      -- Add ourselves to tcBinders for siblings (forward-only
      -- references — later siblings see, earlier ones don't).
      let nextBinders = extendTc n path binders
      pure (dataDecl ann n params e ds, nextBinders)

    ctorD = do
      n   <- identifier
      void (symbol ":")
      e   <- expr (extendPath PsCtorTy path) binders
      ann <- freshDeclAnn
      pure (ctorDecl ann n e, binders)

program
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => m (r a 'SProg)
program = do
  sc
  (ds, _) <- sepEndByIndexedAcc
               (\i bs -> decl (extendPath (PsProgDecl i) emptyPath) bs)
               (symbol ";")
               emptyBinders
  ann <- freshProgAnn
  eof
  pure (prog ann ds)

parseProgram
  :: (Lang r, HasAnn a Parser)
  => FilePath
  -> Text
  -> Either (ParseErrorBundle Text Void) (r a 'SProg)
parseProgram = runParser program
