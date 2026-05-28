{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Grammar functions written generically against any annotation regime
--   via 'HasAnn'.  The parser monad is polymorphic in @m@; concrete
--   runners pick a monad and an annotation type at the call site.
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
keywords = ["data"]

identifier :: (MonadParsec Void Text m, MonadFail m) => m Name
identifier = lexeme . try $ do
  s <- (:) <$> satisfy isAlpha <*> many (satisfy isAlphaNumOrUnder)
  let t = T.pack s
  if t `elem` keywords
    then fail ("keyword " <> show s <> " used as identifier")
    else pure t
  where
    isAlphaNumOrUnder c = isAlphaNum c || c == '_' || c == '\''

starLit :: (Lang r, HasAnn a m, MonadParsec Void Text m) => m (r a 'SExpr)
starLit = lexeme $ do
  void (char '*')
  n   <- L.decimal
  ann <- freshExprAnn
  pure (star ann n)

atom :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m) => m (r a 'SExpr)
atom = choice
  [ starLit
  , do
      n   <- identifier
      ann <- freshExprAnn
      pure (var ann n)
  , between (symbol "(") (symbol ")") expr
  ]

expr :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m) => m (r a 'SExpr)
expr = do
  a <- atom
  option a $ do
    void (symbol "->")
    b   <- expr
    ann <- freshExprAnn
    pure (arr ann a b)

decl :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m) => m (r a 'SDecl)
decl = dataD <|> ctorD
  where
    dataD = do
      void (symbol "data")
      n   <- identifier
      void (symbol ":")
      e   <- expr
      ds  <- between (symbol "{") (symbol "}") (decl `sepEndBy` symbol ";")
      ann <- freshDeclAnn
      pure (dataDecl ann n e ds)

    ctorD = do
      n   <- identifier
      void (symbol ":")
      e   <- expr
      ann <- freshDeclAnn
      pure (ctorDecl ann n e)

program :: (Lang r, HasAnn a m, MonadParsec Void Text m, MonadFail m) => m (r a 'SProg)
program = do
  sc
  ds  <- decl `sepEndBy` symbol ";"
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
