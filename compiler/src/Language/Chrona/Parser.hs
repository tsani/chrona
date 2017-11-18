module Language.Chrona.Parser where

import Data.Annotation
import Data.HFunctor
import Data.HFunctor.Basic
import Language.Chrona.Types
import Language.Chrona.Parser.Types

import Data.Text ( Text, pack )
import Text.Megaparsec
import Text.Megaparsec.String

-- | Space consumer.
sc :: Parser ()
sc = hidden $ many (ch <|> lc) *> pure () where
  ch = spaceChar *> pure ()
  lc = try (string "--") *> manyTill anyChar newline *> pure ()

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

-- | Combine two spans into a span that spans both spans.
--
-- Warning: the spans must be given in order.
joinSpan :: SrcSpan -> SrcSpan -> SrcSpan
joinSpan (SrcSpan start _) (SrcSpan _ end) = SrcSpan start end

kwData, kwCodata, kwLet, kwIn, kwModule, kwFun :: String
kwData = "data"
kwCodata = "codata"
kwLet = "let"
kwIn = "in"
kwModule = "module"
kwFun = "fun"

reservedWords :: [String]
reservedWords =
  [ kwData
  , kwCodata
  , kwLet
  , kwIn
  , kwModule
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

identCore :: (Text -> ASTF (HFix (IAnn (K SrcSpan) ASTF)) n) -> Parser (SrcAST n)
identCore f = do
  (sp, i) <- identifier'
  pure $ HFix (IAnn (K sp) (f (pack i)))

identifier :: Parser (SrcAST 'IdentN)
identifier = identCore Identifier where

semi :: Parser ()
semi = symbol' ";"

-- | Run a parser that spits out an unannotated syntax tree whose subtrees are
-- all annotated and annotates it with source position information.
spanAnn
  :: f ~ HFix (SrcAnnF h)
  => Parser (h f a) -> Parser (f a)
spanAnn p = do
  (sp, x) <- spanning p
  pure $ HFix (IAnn (K sp) x)

moduleDecl :: Parser (SrcAST 'ModuleDeclN)
moduleDecl = spanAnn $ do
  keyword' kwModule
  name <- identifier
  semi

  decls <- many topLevelDecl

  pure $ ModuleDecl name decls

topLevelDecl :: Parser (SrcAST 'TopLevelDeclN)
topLevelDecl = spanAnn (TypeDecl <$> typeDecl) <|> termDecl where

termDecl :: Parser (SrcAST 'TopLevelDeclN)
termDecl = spanAnn $ do
  name <- identifier
  ty <- optional $ symbol' ":" *> typ
  symbol' "="
  t <- term
  pure (TermDecl name ty t)

typeDecl :: Parser (SrcAST 'TypeDeclN)
typeDecl = dataDecl <|> codataDecl where
  dataDecl :: Parser (SrcAST 'TypeDeclN)
  dataDecl = spanAnn $ uncurry3 DataDecl <$> common kwData "|" constructor

  codataDecl :: Parser (SrcAST 'TypeDeclN)
  codataDecl = spanAnn $ do
    uncurry3 CodataDecl <$> common kwCodata "&" obs

  common
    :: String -- ^ the keyword to parse
    -> String -- ^ the separator for the constructors/observations
    -> Parser a -- ^ the parser for one constructor/observation
    -> Parser (SrcAST 'IdentN, [SrcAST 'IdentN], [a])
  common kw s p = do
    keyword' kw
    name <- identifier
    params <- many identifier
    symbol' "="
    ps <- p `sepBy` symbol s
    semi
    pure (name, params, ps)

  constructor :: Parser (SrcAST 'CtorN)
  constructor = spanAnn $ (uncurry ConstructorDef <$> common2)

  obs :: Parser (SrcAST 'ObsN)
  obs = spanAnn $ (uncurry DestructorDef <$> common2)

  -- parse a name followed by an type
  -- e.g.
  common2 = do
    name <- identifier
    ty <- typ
    pure $ (name, ty)

parens :: Parser a -> Parser a
parens = between (symbol' "(") (symbol' ")")

term :: Parser (SrcAST 'ExprN)
term = parens term <|> spanAnn (choice [funExpr, var, app]) where
  var = Var <$> identifier

  app = App <$> term <*> term

  funExpr :: Parser (ASTF SrcAST 'ExprN)
  funExpr = try (keyword' kwFun) *> (Fun <$> (equation `sepBy` symbol "|")) where
    equation :: Parser (SrcAST 'FunEquationN)
    equation = spanAnn $ do
      p <- copattern
      symbol' "->"
      t <- term
      pure $ FunEquation p t

copattern :: Parser (SrcAST 'CopatternN)
copattern = spanAnn $ choice
  [ CopatternPattern <$> pattern <*> copattern
  , ObservationCopattern <$> observation <*> copattern
  , pure EmptyCopattern
  ]

observation :: Parser (SrcAST 'ObservationN)
observation = spanAnn $ try $ Observation <$> (string "." *> identifier)

pattern :: Parser (SrcAST 'PatternN)
pattern = parens pattern <|> spanAnn ps where
  ps = choice
    [ parens (PairPattern <$> (pattern <* symbol ",") <*> pattern)
    , ConstructorPattern <$> identifier <*> pattern
    , PatternVar <$> identifier
    ]

typ :: Parser (SrcAST 'TypeN)
typ = spanAnn (ArrowType <$> typ1 <*> typ1) <|> typ1 where
  typ1 = spanAnn (ProductType <$> typ2 <*> typ2) <|> typ2 where
    typ2 = spanAnn (Next <$> typ3) <|> typ3 where
      typ3 = spanAnn (NamedType <$> typename) <|> parens typ where
        typename :: Parser (SrcAST 'TypeNameN)
        typename = spanAnn $ TypeName <$> identifier where



uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z
