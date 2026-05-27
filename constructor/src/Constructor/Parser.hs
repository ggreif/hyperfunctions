{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Constructor.Parser
  ( parseProgram
  , Parser
  ) where

import Constructor.Sort (Sort (..))
import Constructor.Syntax (Lang (..), Name)
import Control.Monad (void)
import Data.Char (isAlpha, isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void Text

-- | Whitespace + line/block comments.
sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

-- | Reserved words that cannot serve as identifiers.
keywords :: [Text]
keywords = ["data"]

identifier :: Parser Name
identifier = lexeme . try $ do
  s <- (:) <$> satisfy isAlpha <*> many (satisfy isAlphaNumOrUnder)
  let t = T.pack s
  if t `elem` keywords
    then fail ("keyword " <> show s <> " used as identifier")
    else pure t
  where
    isAlphaNumOrUnder c = isAlphaNum c || c == '_' || c == '\''

starLit :: Lang r => Parser (r 'SExpr)
starLit = lexeme $ do
  void (char '*')
  n <- L.decimal
  pure (star n)

-- | An atomic expression: identifier, star, or parenthesised expression.
atom :: Lang r => Parser (r 'SExpr)
atom = choice
  [ starLit
  , var <$> identifier
  , between (symbol "(") (symbol ")") expr
  ]

-- | Expression with right-associative '->'.
expr :: Lang r => Parser (r 'SExpr)
expr = do
  a <- atom
  option a (symbol "->" *> (arr a <$> expr))

-- | One declaration inside a 'data' body.
decl :: Lang r => Parser (r 'SDecl)
decl = dataD <|> ctorD
  where
    dataD = do
      void (symbol "data")
      n <- identifier
      void (symbol ":")
      e <- expr
      ds <- braces (decl `sepEndBy` symbol ";")
      pure (dataDecl n e ds)

    ctorD = do
      n <- identifier
      void (symbol ":")
      e <- expr
      pure (ctorDecl n e)

    braces = between (symbol "{") (symbol "}")

-- | A top-level program: a sequence of declarations separated by ';'.
program :: Lang r => Parser (r 'SProg)
program = do
  sc
  ds <- decl `sepEndBy` symbol ";"
  eof
  pure (prog ds)

-- | Parse a 'Text' input into a program in the user's chosen carrier.
parseProgram
  :: Lang r
  => FilePath          -- ^ source name (for error messages)
  -> Text              -- ^ input
  -> Either (ParseErrorBundle Text Void) (r 'SProg)
parseProgram = runParser program
