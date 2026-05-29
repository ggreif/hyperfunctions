{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Grammar functions written generically against any annotation regime
--   via 'HasAnn'.  The parser monad is polymorphic in @m@; concrete
--   runners pick a monad and an annotation type at the call site.
--
--   The grammar tracks level-variable binders explicitly via a 'Set
--   Name' threaded through the recursive descent.  Inside an outer
--   @∀l. expr@ (or @forall l. expr@), references @*l@ and @*(l + n)@
--   parse to 'starVar'; outside, they parse to a regular 'var'
--   reference (which the typechecker will still reject for level
--   positions, but the parser stays carrier-agnostic).
module Constructor.Parser
  ( parseProgram
  , program
  , Parser
  , RawTree
  ) where

import Constructor.AST (Tree)
import Constructor.Sort (Sort (..))
import Constructor.Syntax (HasAnn (..), Lang (..), Name)
import Control.Monad (void)
import Data.Char (isAlpha, isAlphaNum)
import Data.Functor.Const (Const (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- | The concrete raw parser monad.  Other phases will stack their own
--   transformers on top (e.g. constraint generation) and use
--   'program' directly.
type Parser = Parsec Void Text

-- | Convenience alias for the raw-phase tree: untagged @Const ()@ at
--   every annotation slot.
type RawTree s = Tree (Const ()) s

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

-- | Universe expression starting with @*@.  Three forms:
--
--     *n              -- literal universe at level @n@
--     *l              -- bare variable reference (l must be in scope)
--     *(l + n)        -- variable + literal offset
universe
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Set Name
  -> m (r a 'SExpr)
universe lvs = lexeme $ do
  void (char '*')
  choice
    [ try $ do
        n   <- L.decimal
        ann <- freshExprAnn
        pure (star ann n)
    , between (symbol "(") (symbol ")") $ do
        n <- identifier
        if Set.member n lvs
          then do
            offset <- option 0 (symbol "+" *> L.decimal)
            ann    <- freshExprAnn
            pure (starVar ann n offset)
          else fail ("unbound level variable: " <> T.unpack n)
    , do
        n <- identifier
        if Set.member n lvs
          then do
            ann <- freshExprAnn
            pure (starVar ann n 0)
          else fail ("unbound level variable: " <> T.unpack n)
    ]

atom
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Set Name
  -> m (r a 'SExpr)
atom lvs = choice
  [ universe lvs
  , do
      n   <- identifier
      ann <- freshExprAnn
      pure (var ann n)
  , between (symbol "(") (symbol ")") (expr lvs)
  ]

-- | @∀l. expr@ or @forall l. expr@ — level-binder introduction.  The
--   bound name is added to @lvs@ while parsing the body.
forallExpr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Set Name
  -> m (r a 'SExpr)
forallExpr lvs = do
  void (symbol "\8704" <|> symbol "forall")
  n <- identifier
  void (symbol ".")
  body <- expr (Set.insert n lvs)
  ann  <- freshExprAnn
  pure (forallLv ann n body)

expr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Set Name
  -> m (r a 'SExpr)
expr lvs = forallExpr lvs <|> arrowExpr lvs

arrowExpr
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Set Name
  -> m (r a 'SExpr)
arrowExpr lvs = do
  a <- atom lvs
  option a $ do
    void (symbol "->")
    b   <- expr lvs
    ann <- freshExprAnn
    pure (arr ann a b)

decl
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => Set Name
  -> m (r a 'SDecl)
decl lvs = dataD <|> ctorD
  where
    dataD = do
      void (symbol "data")
      n   <- identifier
      void (symbol ":")
      e   <- expr lvs
      -- Inside the data body, the outer ∀-scope does NOT carry over —
      -- forall scopes to the type annotation only.
      ds  <- between (symbol "{") (symbol "}") (decl Set.empty `sepEndBy` symbol ";")
      ann <- freshDeclAnn
      pure (dataDecl ann n e ds)

    ctorD = do
      n   <- identifier
      void (symbol ":")
      e   <- expr lvs
      ann <- freshDeclAnn
      pure (ctorDecl ann n e)

program
  :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m)
  => m (r a 'SProg)
program = do
  sc
  ds  <- decl Set.empty `sepEndBy` symbol ";"
  ann <- freshProgAnn
  eof
  pure (prog ann ds)

-- | Parse a 'Text' input into a program in the user's chosen carrier
--   and annotation.  The annotation type often needs to be supplied
--   explicitly at the call site (e.g. @parseProgram \@Tree \@(Const ())@).
parseProgram
  :: (Lang r, HasAnn a Parser)
  => FilePath
  -> Text
  -> Either (ParseErrorBundle Text Void) (r a 'SProg)
parseProgram = runParser program
