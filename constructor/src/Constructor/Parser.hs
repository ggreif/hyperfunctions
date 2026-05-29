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
import Control.Monad (void)
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

-- | Map from a level-binder's surface name to the 'Path' of its '∀'
--   introduction.  Threaded explicitly through the grammar.
type LvBinders = Map Name Path

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

-- | Parse a list of grammar elements separated by @sep@, passing each
--   one its sibling index via the supplied parser builder.  Used to
--   give each top-level / inner declaration its own path step.
sepEndByIndexed
  :: MonadParsec e s mm => (Int -> mm a) -> mm b -> mm [a]
sepEndByIndexed mk sep = go 0
  where
    go i = do
      mx <- optional (try (mk i))
      case mx of
        Nothing -> pure []
        Just x  -> do
          msep <- optional sep
          case msep of
            Nothing -> pure [x]
            Just _  -> (x :) <$> go (i + 1)

-- ----------------------------------------------------------------------
-- Expression-level parsers.
-- ----------------------------------------------------------------------

-- | Universe expression starting with @*@.
universe
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> LvBinders -> m (r a 'SExpr)
universe _path binders = lexeme $ do
  void (char '*')
  choice
    [ try $ do
        n   <- L.decimal
        ann <- freshExprAnn
        pure (star ann n)
    , between (symbol "(") (symbol ")") $ do
        n <- identifier
        case Map.lookup n binders of
          Just binderPath -> do
            offset <- option 0 (symbol "+" *> L.decimal)
            ann    <- freshExprAnn
            pure (starVar ann n binderPath offset)
          Nothing -> fail ("unbound level variable: " <> T.unpack n)
    , do
        n <- identifier
        case Map.lookup n binders of
          Just binderPath -> do
            ann <- freshExprAnn
            pure (starVar ann n binderPath 0)
          Nothing -> fail ("unbound level variable: " <> T.unpack n)
    ]

atom
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> LvBinders -> m (r a 'SExpr)
atom path binders = choice
  [ universe path binders
  , do
      n   <- identifier
      ann <- freshExprAnn
      pure (var ann n)
  , between (symbol "(") (symbol ")") (expr (extendPath PsParens path) binders)
  ]

-- | @∀l. expr@ — level-binder introduction.  The binder's 'Path' is
--   the *current* path (where the @∀@ sits); the body is parsed at
--   @path ++ [PsForallBody]@ with the binder added to scope.
forallExpr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> LvBinders -> m (r a 'SExpr)
forallExpr path binders = do
  void (symbol "\8704" <|> symbol "forall")
  n <- identifier
  void (symbol ".")
  let binderPath = path
      binders'   = Map.insert n binderPath binders
  body <- expr (extendPath PsForallBody path) binders'
  ann  <- freshExprAnn
  pure (forallLv ann n binderPath body)

expr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> LvBinders -> m (r a 'SExpr)
expr path binders = forallExpr path binders <|> arrowExpr path binders

arrowExpr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> LvBinders -> m (r a 'SExpr)
arrowExpr path binders = do
  a <- atom (extendPath PsArrL path) binders
  option a $ do
    void (symbol "->")
    b   <- expr (extendPath PsArrR path) binders
    ann <- freshExprAnn
    pure (arr ann a b)

-- ----------------------------------------------------------------------
-- Declaration-level parsers.
-- ----------------------------------------------------------------------

decl
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Path -> LvBinders -> m (r a 'SDecl)
decl path binders = dataD <|> ctorD
  where
    dataD = do
      void (symbol "data")
      n   <- identifier
      void (symbol ":")
      e   <- expr (extendPath PsDataAnn path) binders
      -- Inside the data body, the outer ∀-scope does NOT carry over.
      ds  <- between (symbol "{") (symbol "}") $
               sepEndByIndexed
                 (\i -> decl (extendPath (PsDeclIdx i) path) Map.empty)
                 (symbol ";")
      ann <- freshDeclAnn
      pure (dataDecl ann n e ds)

    ctorD = do
      n   <- identifier
      void (symbol ":")
      e   <- expr (extendPath PsCtorTy path) binders
      ann <- freshDeclAnn
      pure (ctorDecl ann n e)

program
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => m (r a 'SProg)
program = do
  sc
  ds  <- sepEndByIndexed
           (\i -> decl (extendPath (PsProgDecl i) emptyPath) Map.empty)
           (symbol ";")
  ann <- freshProgAnn
  eof
  pure (prog ann ds)

parseProgram
  :: (Lang r, HasAnn a Parser)
  => FilePath
  -> Text
  -> Either (ParseErrorBundle Text Void) (r a 'SProg)
parseProgram = runParser program
