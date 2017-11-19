module Language.Chrona.Parser.Lexer where

import Language.Chrona.Parser.Core

-- | Space consumer.
sc :: Parser ()
sc = hidden $ many (ch <|> lc) *> pure () where
  ch = spaceChar *> pure ()
  lc = try (symbol' symComment) *> manyTill anyChar newline *> pure ()

-- | Makes a parser gobble up spaces after.
lexeme :: Parser a -> Parser a
lexeme p = p <* sc

-- | Runs a parser and obtains the span of text traversed by it.
spanning :: Parser a -> Parser (SrcSpan, a)
spanning p = do
  start <- getPosition
  x <- p
  end <- getPosition
  pure (SrcSpan start end, x)

reservedWords :: [String]
reservedWords =
  [ kwData
  , kwCodata
  , kwLet
  , kwIn
  , kwModule
  , kwFun
  ]

-- | Parser that succeeds only if a reserved word is matched.
someReservedWord :: Parser ()
someReservedWord = () <$ choice ps where
  ps = (\s -> (string s :: Parser String) <* notFollowedBy identTail) <$> reservedWords

-- | Keywords are parsed the same way as identifiers, but must equal a given
-- string rather than be arbitrary.
keyword :: String -> Parser String
keyword s = lexeme (try (string s) <* notFollowedBy alphaNumChar)

keyword' :: String -> Parser ()
keyword' = (() <$) . keyword

symbol :: String -> Parser String
symbol s = lexeme (try (string s) <* notFollowedBy symbolChar)

symbol' :: String -> Parser ()
symbol' = (() <$) . symbol

identifier' :: Parser (SrcSpan, String)
identifier'
  = notFollowedBy someReservedWord *> lexeme (spanning p <* notFollowedBy identTail) where
    p = (:) <$> identHead <*> many identTail
    identHead = letterChar

identTail :: Parser Char
identTail = alphaNumChar

semi :: Parser ()
semi = symbol' symSemi

parens :: Parser a -> Parser a
parens = between (symbol' "(") (symbol' ")")

kwData, kwCodata, kwLet, kwIn, kwModule, kwFun :: String
kwData = "data"
kwCodata = "codata"
kwLet = "let"
kwIn = "in"
kwModule = "module"
kwFun = "fun"

symHasType, symEquals, symSemi, symCtorSep, symObsSep, symComment :: String
symHasType = ":"
symEquals = "="
symSemi = ";"
symCtorSep = "|"
symObsSep = "&"
symComment = "--"
