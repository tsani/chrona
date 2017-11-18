module Language.Chrona.Types where

import Data.Reflection
import Data.HFunctor

import Data.Text ( Text )

data Node
  = ModuleDeclN
  | TopLevelDeclN
  | TypeDeclN
  | FunEquationN
  | ExprN
  | TypeN
  | CtorN
  | FieldN
  | ObsN
  | PatternN
  | CopatternN
  | ObservationN
  -- | Identifiers.
  | IdentN
  | TypeNameN

-- | Singletons for 'Node'.
data NodeS (n :: Node) :: * where
  ModuleDeclS :: NodeS 'ModuleDeclN
  TopLevelDeclS :: NodeS 'TopLevelDeclN
  TypeDeclS :: NodeS 'TypeDeclN
  FunEquationS :: NodeS 'FunEquationN
  ExprS :: NodeS 'ExprN
  TypeS :: NodeS 'TypeN
  CtorS :: NodeS 'CtorN
  FieldS :: NodeS 'FieldN
  ObsS :: NodeS 'ObsN
  PatternS :: NodeS 'PatternN
  CopatternS :: NodeS 'CopatternN
  ObservationS :: NodeS 'ObservationN
  IdentS :: NodeS 'IdentN
  TypeNameS :: NodeS 'TypeNameN

deriving instance Eq (NodeS n)

instance PolyEq NodeS where
  peq n1 n2 = case (n1, n2) of
    (ModuleDeclS, ModuleDeclS) -> True
    (TopLevelDeclS, TopLevelDeclS) -> True
    (TypeDeclS, TypeDeclS) -> True
    (FunEquationS, FunEquationS) -> True
    (ExprS, ExprS) -> True
    (TypeS, TypeS) -> True
    (CtorS, CtorS) -> True
    (FieldS, FieldS) -> True
    (ObsS, ObsS) -> True
    (PatternS, PatternS) -> True
    (CopatternS, CopatternS) -> True
    (ObservationS, ObservationS) -> True
    (IdentS, IdentS) -> True
    (TypeNameS, TypeNameS) -> True
    _ -> False

type instance Demote Node = NodeS

instance Reflect 'ModuleDeclN where reflect _ = ModuleDeclS
instance Reflect 'TopLevelDeclN where reflect _ = TopLevelDeclS
instance Reflect 'TypeDeclN where reflect _ = TypeDeclS
instance Reflect 'FunEquationN where reflect _ = FunEquationS
instance Reflect 'ExprN where reflect _ = ExprS
instance Reflect 'TypeN where reflect _ = TypeS
instance Reflect 'CtorN where reflect _ = CtorS
instance Reflect 'FieldN where reflect _ = FieldS
instance Reflect 'ObsN where reflect _ = ObsS
instance Reflect 'PatternN where reflect _ = PatternS
instance Reflect 'CopatternN where reflect _ = CopatternS
instance Reflect 'ObservationN where reflect _ = ObservationS
instance Reflect 'IdentN where reflect _ = IdentS
instance Reflect 'TypeNameN where reflect _ = TypeNameS

class Elem (x :: k) (l :: [k]) where
instance {-# OVERLAPPING #-} Elem x (x ': xs) where
instance Elem x xs => Elem x (y ': xs) where

data ASTF :: (Node -> *) -> Node -> * where
  ModuleDecl
    :: ast 'IdentN -- name of the module
    -> [ast 'TopLevelDeclN] -- the top level declarations
    -> ASTF ast 'ModuleDeclN

  ---- TERM DEFINITION LANGUAGE

  TermDecl
    :: ast 'IdentN
    -> Maybe (ast 'TypeN)
    -> ast 'ExprN
    -> ASTF ast 'TopLevelDeclN

  ---- TYPE DEFINITION LANGUAGE

  DataDecl
    :: ast 'IdentN -- the name of the type
    -> [ast 'IdentN] -- the names of any type parameters
    -> [ast 'CtorN] -- the constructors
    -> ASTF ast 'TypeDeclN

  CodataDecl
    :: ast 'IdentN -- the name of the type
    -> [ast 'IdentN] -- the names of any type parameters
    -> [ast 'ObsN] -- the observations
    -> ASTF ast 'TypeDeclN

  TypeDecl
    :: ast 'TypeDeclN
    -> ASTF ast 'TopLevelDeclN

  ConstructorDef
    :: ast 'IdentN -- name of the constructor
    -> ast 'TypeN -- type of its input
    -> ASTF ast 'CtorN

  DestructorDef
    :: ast 'IdentN -- the name of the observation
    -> ast 'TypeN -- type of its output
    -> ASTF ast 'ObsN

  ---- PATTERN LANGUAGE

  -- | An empty copattern; these are never written explicitly by the user.
  EmptyCopattern
    :: ASTF ast 'CopatternN

  -- A pattern followed by another copattern.
  CopatternPattern
    :: ast 'PatternN
    -> ast 'CopatternN
    -> ASTF ast 'CopatternN

  -- | An observation followed by another copattern.
  ObservationCopattern
    :: ast 'ObservationN
    -> ast 'CopatternN
    -> ASTF ast 'CopatternN

  -- | A variable.
  PatternVar
    :: ast 'IdentN
    -> ASTF ast 'PatternN

  PairPattern
    :: ast 'PatternN
    -> ast 'PatternN
    -> ASTF ast 'PatternN

  -- | A constructor can be used as a pattern to perform pattern matching.
  -- Following the constructor is a patterns for its field.
  ConstructorPattern
    :: ast 'IdentN
    -> ast 'PatternN
    -> ASTF ast 'PatternN

  -- | A variable but that doesn't introduce a binding.
  UnderscorePattern
    :: ASTF ast 'PatternN

  ---- TYPE LANGUAGE

  ArrowType
    :: ast 'TypeN
    -> ast 'TypeN
    -> ASTF ast 'TypeN

  ProductType
    :: ast 'TypeN
    -> ast 'TypeN
    -> ASTF ast 'TypeN

  Next
    :: ast 'TypeN
    -> ASTF ast 'TypeN

  NamedType
    :: ast 'TypeNameN
    -- -> [ast 'TypeN] -- type parameters
    -- we disallow type parameters for now; this should actually be a
    -- type-level application construct tbh
    -> ASTF ast 'TypeN

  ---- MISC

  TypeName
    :: ast 'IdentN
    -> ASTF ast 'TypeNameN

  Identifier
    :: Text
    -> ASTF ast 'IdentN

  ---- TERM LANGUAGE

  Fun
    :: [ast 'FunEquationN]
    -- the equations that define the function
    -> ASTF ast 'ExprN

  FunEquation
    :: ast 'CopatternN
    -> ast 'ExprN
    -> ASTF ast 'FunEquationN

  App
    :: ast 'ExprN
    -> ast 'ExprN
    -> ASTF ast 'ExprN

  Var
    :: ast 'IdentN
    -> ASTF ast 'ExprN

  ObservationExpr
    :: ast 'ObservationN
    -> ASTF ast 'ExprN

  Observation
    :: ast 'IdentN
    -> ASTF ast 'ObservationN

-- | Extracts the textual representation of an identifier.
ident :: HFix ASTF 'IdentN -> Text
ident (HFix (Identifier t)) = t

typeName :: HFix ASTF 'TypeNameN -> Text
typeName (HFix (TypeName i)) = ident i

instance HFunctor ASTF where
  hfmap nat h = case h of
    ModuleDecl i ds -> ModuleDecl (nat i) (nat <$> ds)
    TermDecl i m e -> TermDecl (nat i) (nat <$> m) (nat e)
    TypeDecl d -> TypeDecl (nat d)
    DataDecl i is cs -> DataDecl (nat i) (nat <$> is) (nat <$> cs)
    CodataDecl i is os -> CodataDecl (nat i) (nat <$> is) (nat <$> os)
    ConstructorDef i t -> ConstructorDef (nat i) (nat t)
    DestructorDef i t -> DestructorDef (nat i) (nat t)
    EmptyCopattern -> EmptyCopattern
    CopatternPattern p c -> CopatternPattern (nat p) (nat c)
    ObservationCopattern o c -> ObservationCopattern (nat o) (nat c)
    PatternVar i -> PatternVar (nat i)
    PairPattern p1 p2 -> PairPattern (nat p1) (nat p2)
    ConstructorPattern i p -> ConstructorPattern (nat i) (nat p)
    UnderscorePattern -> UnderscorePattern
    ArrowType t1 t2 -> ArrowType (nat t1) (nat t2)
    ProductType t1 t2 -> ProductType (nat t1) (nat t2)
    Next t -> Next (nat t)
    NamedType i -> NamedType (nat i)
    Identifier t -> Identifier t
    Fun eqs -> Fun (nat <$> eqs)
    FunEquation c e -> FunEquation (nat c) (nat e)
    App e1 e2 -> App (nat e1) (nat e2)
    Var i -> Var (nat i)
    ObservationExpr o -> ObservationExpr (nat o)
    Observation i -> Observation (nat i)
    TypeName i -> TypeName (nat i)

instance HTraversable ASTF where
  sequenceH node = case node of
    ModuleDecl (Compose i) (traverse getCompose -> ds) ->
      ModuleDecl <$> i <*> ds
    TermDecl (Compose i) (traverse getCompose -> m) (Compose e) ->
      TermDecl <$> i <*> m <*> e
    TypeDecl (Compose d) -> TypeDecl <$> d
    DataDecl (Compose i) (traverse getCompose -> is) (traverse getCompose -> cs) ->
      DataDecl <$> i <*> is <*> cs
    CodataDecl (Compose i) (traverse getCompose -> is) (traverse getCompose -> os) ->
      CodataDecl <$> i <*> is <*> os
    ConstructorDef (Compose i) (Compose t) ->
      ConstructorDef <$> i <*> t
    DestructorDef (Compose i) (Compose t) ->
      DestructorDef <$> i <*> t
    EmptyCopattern -> pure EmptyCopattern
    CopatternPattern (Compose p) (Compose c) ->
      CopatternPattern <$> p <*> c
    ObservationCopattern (Compose o) (Compose c) ->
      ObservationCopattern <$> o <*> c
    PatternVar (Compose i) ->
      PatternVar <$> i
    PairPattern (Compose p1) (Compose p2) ->
      PairPattern <$> p1 <*> p2
    ConstructorPattern (Compose i) (Compose p) ->
      ConstructorPattern <$> i <*> p
    UnderscorePattern -> pure UnderscorePattern
    ArrowType (Compose t1) (Compose t2) ->
      ArrowType <$> t1 <*> t2
    ProductType (Compose t1) (Compose t2) ->
      ProductType <$> t1 <*> t2
    Next (Compose t) ->
      Next <$> t
    NamedType (Compose i) ->
      NamedType <$> i
    Identifier t -> pure (Identifier t)
    Fun (traverse getCompose -> eqs) ->
      Fun <$> eqs
    FunEquation (Compose c) (Compose e) ->
      FunEquation <$> c <*> e
    App (Compose e1) (Compose e2) ->
      App <$> e1 <*> e2
    Var (Compose i) ->
      Var <$> i
    ObservationExpr (Compose o) ->
      ObservationExpr <$> o
    Observation (Compose i) ->
      Observation <$> i
    TypeName (Compose i) -> TypeName <$> i

-- | Collapse the indices for a syntax tree.
-- This helps make certain pattern matches more succint.
collapseIndex :: ASTF ast node -> NodeS node
collapseIndex node = case node of
  ModuleDecl _ _ -> ModuleDeclS
  TermDecl _ _ _ -> TopLevelDeclS
  TypeDecl _ -> TopLevelDeclS
  DataDecl _ _ _ -> TypeDeclS
  CodataDecl _ _ _ -> TypeDeclS
  ConstructorDef _ _ -> CtorS
  DestructorDef _ _ -> ObsS
  EmptyCopattern -> CopatternS
  CopatternPattern _ _ -> CopatternS
  ObservationCopattern _ _ -> CopatternS
  PatternVar _ -> PatternS
  PairPattern _ _ -> PatternS
  ConstructorPattern _ _ -> PatternS
  UnderscorePattern -> PatternS
  ArrowType _ _ -> TypeS
  ProductType _ _ -> TypeS
  Next _ -> TypeS
  NamedType _ -> TypeS
  TypeName _ -> TypeNameS
  Identifier _ -> IdentS
  Fun _ -> ExprS
  FunEquation _ _ -> FunEquationS
  App _ _ -> ExprS
  Var _ -> ExprS
  ObservationExpr _ -> ExprS
  Observation _ -> ObservationS
