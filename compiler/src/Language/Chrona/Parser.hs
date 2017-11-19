module Language.Chrona.Parser
( parseChronaProgram
) where

import Data.Annotation
import Data.HFunctor
import Data.HFunctor.Basic
import Language.Chrona.Types
import Language.Chrona.Parser.Core
import Language.Chrona.Parser.Lexer

import Data.Text ( Text, pack )

identCore :: (Text -> ASTF (HFix (IAnn (K SrcSpan) ASTF)) n) -> Parser (SrcAST n)
identCore f = do
  (sp, i) <- identifier'
  pure $ HFix (IAnn (K sp) (f (pack i)))

identifier :: Parser (SrcAST 'IdentN)
identifier = identCore Identifier where

-- | Run a parser that spits out an unannotated syntax tree whose subtrees are
-- all annotated and annotates it with source position information.
spanAnn
  :: f ~ HFix (SrcAnnF h)
  => Parser (h f a) -> Parser (f a)
spanAnn p = do
  (sp, x) <- spanning p
  pure $ HFix (IAnn (K sp) x)

parseChronaProgram
  :: FilePath
  -> String
  -> Either (ParseError Char Dec) (SrcAST 'ModuleDeclN)
parseChronaProgram = parse moduleDecl

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
  ty <- optional $ symbol' symHasType *> typ
  symbol' symEquals
  t <- term
  pure (TermDecl name ty t)

typeDecl :: Parser (SrcAST 'TypeDeclN)
typeDecl = dataDecl <|> codataDecl where
  dataDecl :: Parser (SrcAST 'TypeDeclN)
  dataDecl = spanAnn $ uncurry3 DataDecl <$> common kwData symCtorSep constructor

  codataDecl :: Parser (SrcAST 'TypeDeclN)
  codataDecl = spanAnn $ do
    uncurry3 CodataDecl <$> common kwCodata symObsSep obs

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

  uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
  uncurry3 f (x, y, z) = f x y z

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
