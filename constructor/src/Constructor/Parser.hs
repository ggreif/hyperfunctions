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

-- | Lookahead-scan the body @{ decl1; decl2; … }@ that's about to
--   be parsed, harvesting each decl's name + path so the body can
--   then be parsed with all siblings already in 'tcBinders'.
--   Required for mutual references inside a data body — e.g. @data
--   Swap : Swap { Left : Right; Right : Left }@ where each ctor's
--   type mentions a sibling ctor.  Without the prescan, the
--   forward-only accumulator pattern in 'sepEndByIndexedAcc' would
--   only let later siblings see earlier ones.
--
--   This is a /name/-only scan: it advances the cursor past the
--   first identifier of each decl (skipping the optional 'data'
--   keyword), then skips the rest of the decl by consuming tokens
--   until the next top-level @;@ or the closing @}@.  Balanced
--   braces inside nested data bodies are tracked so a nested @data
--   Inner : *0 { … }@ doesn't fool the outer scan.  Block comments
--   are handled by interleaving 'sc' (the lexer's space-and-comment
--   skipper) before each character peek.
-- | Top-level analog: 'prescanBodyDeclNames' but without the outer
--   @{@/@}@ wrappers — terminator is EOF.  Used by 'program' to
--   harvest top-level data names so they're all in 'tcBinders'
--   before any top-level decl is elaborated, giving Haskell-module
--   /Agda-mutual-block style implicit mutual recursion at the
--   program scope.
prescanProgramDeclNames
  :: (MonadParsec Void Text m, MonadFail m)
  => m [(Name, Path)]
prescanProgramDeclNames = lookAhead (collectTop 0 [])
  where
    collectTop i acc = do
      sc
      done <- atEnd
      if done
        then pure (reverse acc)
        else do
          name <- declHeadName_
          let declPath = extendPath (PsProgDecl i) emptyPath
          skipDeclBody_ 0
          msep <- optional (symbol ";")
          let acc' = (name, declPath) : acc
          case msep of
            Just _  -> collectTop (i + 1) acc'
            Nothing -> pure (reverse acc')

    declHeadName_ = do
      _ <- optional (try (symbol "data"))
      identifier

    skipDeclBody_ depth = do
      sc
      mc <- optional (lookAhead anySingle)
      case mc of
        Nothing -> pure ()  -- EOF
        Just c -> case c of
          '{' -> do
            void (single '{')
            skipDeclBody_ (depth + 1)
          '}'
            | depth == 0 -> pure ()  -- shouldn't happen at top level; bail
            | otherwise -> do
                void (single '}')
                skipDeclBody_ (depth - 1)
          ';' | depth == 0 -> pure ()
          _   -> do
            void anySingle
            skipDeclBody_ depth

prescanBodyDeclNames
  :: (MonadParsec Void Text m, MonadFail m)
  => Path -> m [(Name, Path)]
prescanBodyDeclNames parentPath = lookAhead $ do
  void (symbol "{")
  collect 0 []
  where
    collect i acc = do
      sc
      end <- optional (try (lookAhead (single '}')))
      case end of
        Just _ -> pure (reverse acc)
        Nothing -> do
          name <- declHeadName
          let declPath = extendPath (PsDeclIdx i) parentPath
          skipDeclBody 0
          msep <- optional (symbol ";")
          let acc' = (name, declPath) : acc
          case msep of
            Just _  -> collect (i + 1) acc'
            Nothing -> pure (reverse acc')

    declHeadName = do
      _ <- optional (try (symbol "data"))
      identifier

    -- Skip tokens until we see a top-level @;@ or @}@ (depth 0).
    -- Balanced @{...}@ at depth > 0 don't terminate us; comments
    -- are eaten via 'sc' before each peek.
    skipDeclBody depth = do
      sc
      mc <- optional (lookAhead anySingle)
      case mc of
        Nothing -> pure ()  -- EOF
        Just c -> case c of
          '{' -> do
            void (single '{')
            skipDeclBody (depth + 1)
          '}'
            | depth == 0 -> pure ()
            | otherwise -> do
                void (single '}')
                skipDeclBody (depth - 1)
          ';' | depth == 0 -> pure ()
          _   -> do
            void anySingle
            skipDeclBody depth

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
--   @f x y z@ parses to @app (app (app f x) y) z@.  Every nested
--   'App' built by this fold shares the same 'Path' — namely the
--   path of the application as a whole — so carriers that allocate
--   fresh metavariables at parametric tycon use-sites address them
--   uniformly within one syntactic application.
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
      pure (app ann path f x)

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
      -- Pre-extend the binders with @n@ BEFORE parsing the kind
      -- annotation, so a self-referential annotation (the @data
      -- Weird : Weird@ shape) resolves the inner @n@ to a
      -- 'tyConRef' rather than a generic 'var'.  Downstream
      -- carriers (HypTinf, HypTwr) have no 'var' lookup table; an
      -- un-pre-bound annotation would mask the self-reference at
      -- parse time as 'Var "Weird"' and then fail with TyUnbound
      -- when the polymorphic re-emit reaches the type layer.
      let annBinders = extendTc n path binders
      e   <- towerOrAnnotated n path PsDataAnn annBinders
      -- Inside the data body, the outer ∀-scope does NOT carry over,
      -- but: the data's own type parameters DO (scoped over each
      -- constructor's type), the data binder itself DOES (so
      -- constructors can mention the type they construct, and so
      -- nested data can reference it), and the outer tcBinders DO
      -- (top-level tycons remain visible inside nested bodies).
      --
      -- Plus: PRESCAN sibling names so that mutual references
      -- between body decls resolve correctly to 'tyConRef'.  E.g.
      -- @data Swap : Swap { Left : Right; Right : Left }@ has Left
      -- and Right referring to each other; without the prescan,
      -- 'Right' in 'Left : Right' would be a 'var' and HypTinf /
      -- HypTwr would fail with TyUnbound.  The prescan uses
      -- 'lookAhead' so it doesn't consume input — names are
      -- harvested first, then the body is parsed for real.
      siblingNames <- prescanBodyDeclNames path
      let paramPaths   = zipWith (\i p -> (p, extendPath (PsDataParam i) path))
                                 [0 ..] params
          bodyBinders0 = binders { lvBinders = Map.empty }
          bodyBinders  = foldr (\(sn, sp) -> extendTc sn sp)
                               (extendTc n path (extendTys paramPaths bodyBinders0))
                               siblingNames
      (ds, _)  <- between (symbol "{") (symbol "}") $
                    sepEndByIndexedAcc
                      (\i bs -> decl (extendPath (PsDeclIdx i) path) bs)
                      (symbol ";")
                      bodyBinders
      ann <- freshDeclAnn
      -- Add ourselves to tcBinders for siblings (forward-only
      -- references — later siblings see, earlier ones don't).
      let nextBinders = extendTc n path binders
      pure (dataDecl ann path n params e ds, nextBinders)

    ctorD = do
      n   <- identifier
      e   <- towerOrAnnotated n path PsCtorTy binders
      ann <- freshDeclAnn
      pure (ctorDecl ann n e, binders)

    -- | Either @: expr@ or @⋮@ (the typing-tower shorthand).  The
    --   '⋮' (U+22EE VERTICAL ELLIPSIS) is /literally/ the typing
    --   tower as glyph — three vertical dots picking out the
    --   stable upward stream of rungs that @predLv (LVar p) = LVar
    --   p@ guarantees.  Parsed as a 'tyConRef' to the LHS
    --   identifier at the LHS path: the right reading is "build the
    --   tower at this name+path, use its next rung as the type
    --   annotation" — which is precisely 'kindOf' applied to that
    --   TyConV at offset zero, giving the same-name-bumped-offset
    --   under self-stratification.
    --
    --   This is shorthand only — semantically equivalent to the
    --   explicit @c : c@ form once the body-mutual prescan + the
    --   self-reference pre-extend put @c@ into tcBinders.
    towerOrAnnotated lhsName lhsPath pathStep bs =
          (do void (symbol "\8942")
              ann' <- freshExprAnn
              pure (tyConRef ann' lhsName lhsPath))
      <|> (do void (symbol ":")
              expr (extendPath pathStep lhsPath) bs)

program
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => m (r a 'SProg)
program = do
  sc
  -- Top-level prescan: harvest all program-level data names BEFORE
  -- iterating, so top-level mutual references between data decls
  -- work without an explicit @mutual { ... }@ block.  Same trick
  -- as the body-mutual prescan in 'dataD' (Agda's @mutual@-style
  -- forward-reference resolution); applied uniformly to all
  -- top-level decls because module-scope mutual is the
  -- Haskell/SML default and our singular use case is mostly
  -- definitional clusters where mutual is the rule.
  programNames <- prescanProgramDeclNames
  let topBinders = foldr (\(n, p) -> extendTc n p) emptyBinders programNames
  (ds, _) <- sepEndByIndexedAcc
               (\i bs -> decl (extendPath (PsProgDecl i) emptyPath) bs)
               (symbol ";")
               topBinders
  ann <- freshProgAnn
  eof
  pure (prog ann ds)

parseProgram
  :: (Lang r, HasAnn a Parser)
  => FilePath
  -> Text
  -> Either (ParseErrorBundle Text Void) (r a 'SProg)
parseProgram = runParser program
