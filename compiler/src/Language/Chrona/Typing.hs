module Language.Chrona.Typing where

import Data.Text ( Text )
import qualified Data.Map as M

import Data.Annotation
import Data.Apply
import Data.HFunctor
import Data.HFunctor.Basic
import Data.HFunctor.TopDown
import Data.Validation
import Language.Chrona.Parser.Types
import Language.Chrona.Types

-- we need to collect all type declarations so we know whether a named type
-- refers to a defined type or is a type variable.

-- first we collect the names of all types declared in the module

-- type family CollectTypes' (node :: Node) :: * where
--   CollectTypes' 'TopLevelDeclN = Maybe Text
--   CollectTypes' 'TypeDeclN = Text
--   CollectTypes' 'ModuleDeclN = [Text]
--   CollectTypes' 'IdentN = Text
--   CollectTypes' a = ()
--
-- newtype CollectTypes (node :: Node)
--   = CollectTypes
--     { collectedTypes :: CollectTypes' node
--     }
--
-- collectTypes
--   :: forall node. HFix ASTF node
--   -> CollectTypes node
-- collectTypes = hcata phi where
--   phi :: forall n. ASTF CollectTypes n -> CollectTypes n
--   phi node = case collapseIndex node of
--     ModuleDeclS -> case node of
--       ModuleDecl _ ts -> CollectTypes $ catMaybes $ collectedTypes <$> ts
--     TopLevelDeclS -> case node of
--       TypeDecl (CollectTypes n) -> CollectTypes (Just n)
--       TermDecl _ _ _ -> CollectTypes Nothing
--     TypeDeclS -> case node of
--       DataDecl (CollectTypes n) _ -> CollectTypes n
--       CodataDecl (CollectTypes n) _ -> CollectTypes n
--     IdentS -> case node of
--       Identifier t -> CollectTypes t
--
--     -- feels bad
--     FunEquationS -> CollectTypes ()
--     ExprS -> CollectTypes ()
--     TypeS -> CollectTypes ()
--     CtorS -> CollectTypes ()
--     ObsS -> CollectTypes ()
--     PatternS -> CollectTypes ()
--     CopatternS -> CollectTypes ()
--     ObservationS -> CollectTypes ()
--     TypeNameS -> CollectTypes ()

-- next we need to check all type names for scoping issues.
-- we annotate each occurrence of NamedType with how the name is bound: either
-- to a type variable or to another type.
-- We use a de Bruijn style representation here: we annotate bound namedtypes
-- with their index into the list and "free" namedtypes are marked
-- free

-- -- | The binding information of a type: either a type is free (refers to
-- -- another datatype in the file) or is bound (refers to a type variable
-- -- introduced by the (co)data declaration).
-- data TypeBinding = TypeFree | TypeBound Int

-- | The universe of types.
data Type
  -- | Base type with one value.
  = Unit
  -- | Pairs.
  | Cross Type Type
  -- | Functions.
  | Function Type Type
  -- | Least fixed-points.
  | Mu Text [Field]
  -- | Greated fixed-points.
  | Nu Text [Field]
  -- | Lax modality.
  | Next Type
  -- | Type variables.
  | Var Text

-- | The type of a field: a constructor or a destructor.
data FieldType = C | D

-- | Annotation function for type checking.
type family TypeCheck' (node :: Node) :: * where
  -- typechecking an expression, we figure out its type
  TypeCheck' 'ExprN = Type

  -- typechecking a pattern, we figure out a context of variables introduced by
  -- the pattern
  TypeCheck' 'PatternN = Gamma

  -- typechecking a copattern, we figure out a context of variables introduced
  -- by its patterns as well as a type synthesized by it
  TypeCheck' 'CopatternN = (Type, Gamma)

  TypeCheck' _ = ()

-- | Represents the type family 'TypeCheck''.
newtype TypeCheck (node :: Node)
  = TypeCheck
    { bindingSite :: TypeCheck' node
    }

type Time = Int

-- | Context of types.
type Delta = M.Map Text (SrcSpan, Type)

-- | Context of values.
type Gamma = M.Map Text (SrcSpan, Time, Type)

-- | Generalizes constructors and observations.
data Field
  = Field
    { fName :: Text
    -- ^ The name of the field.
    , frType :: Type
    -- ^ The type of the field.
    , fOwner :: Text
    -- ^ The name of the type that owns the field.
    }

data Env
  = Env
    { eTypes :: Delta
    -- ^ All known types, identified by name, and associated with their
    -- simple representation.
    , eCurrentType :: Maybe Text
    -- ^ The current type we're processing.
    , eVars :: Delta
    -- ^ The variables in scope, associated to their type and their time.
    , eFields :: M.Map (FieldType, Text) Type
    -- ^ The known destructors and constructors. Used for pattern matching.
    , eTime :: Time
    -- ^ The current time.
    , eCopGoal :: Maybe Type
    -- ^ The goal of the current copattern we're checking.
    }

data Severity
  = WarningSev
  -- ^ An error that still results in code that can be executed, but may have
  -- unintended semantics.
  | ErrorSev
  -- ^ An error that results in code that cannot be executed, but that does not
  -- impede further compilation.
  | FatalSev
  -- ^ An error that results in code that connect be executed and impedes
  -- further compilation.
  | InternalSev
  -- ^ An error that arises due to the violation of an internal invariant.
  -- These errors are compiler bugs.

data Error
  = Error
    { errorSeverity :: Severity
    , errorBody :: ErrorBody
    }

data ErrorBody
  = VScope (VariableNotInScope Gamma)
  | TScope (VariableNotInScope Delta)

data VariableNotInScope scope
  = VariableNotInScope
    { tvName :: Text
    -- ^ The name of the variable that's not in scope.
    , tvInScope :: scope
    -- ^ The variables that are in scope.
    }

initialEnv :: Env
initialEnv = Env
  { eTypes = M.empty
  , eCurrentType = Nothing
  , eVars = M.empty
  , eFields = M.empty
  , eTime = 0
  , eCopGoal = Nothing
  }

lookupVar ::

newtype Check (a :: Node)
  = Check
    (TypeCheck' a, ASTF (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF)) a)

-- to pull off this traversal we need to have some information coming in /from
-- above/: if we enter a type from a function declaration, then free variables
-- are all implicitly bound if they don't refer to an external type; whereas if
-- we enter a type from a (co)data declaration then free variables are simply
-- not permitted. In that case we have to add the bindings introduced by the
-- declaration to the scoping map.
typeCheck
  :: forall node. HFix (PAnn '[K SrcSpan] ASTF) node
  -> Nat
    (K Env)
    (Validation
      [Error]
      (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF)))
    node
typeCheck = hcata (adjust phi) where
  adjust
    :: forall b.
      (forall a. Env
        -> SrcSpan
        -> ASTF
          (Nat
            (K Env)
            (Validation [Error] (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF))))
          a
        -> Validation
          [Error]
          Check
          a
    )
    -> PAnn
        '[K SrcSpan]
        ASTF
        (Nat
          (K Env)
          (Validation
            [Error]
            (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF))))
        b
    -> Nat
      (K Env)
      (Validation
        [Error]
        (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF)))
      b
  adjust f (IAnn a@(PCons (K s) PNil) node) =
    Nat $ \(K env) -> hpure (Nat' (repack a)) <**> f env s node

  repack
    :: forall a. P '[K SrcSpan] a
    -> Check a
    -> HFix (PAnn '[TypeCheck, K SrcSpan] ASTF) a
  repack ps (Check (p, node')) = HFix (IAnn (PCons (TypeCheck p) ps) node')

  phi
    :: forall a. Env
    -> SrcSpan
    -> ASTF
      (Nat
        (K Env)
        (Validation [Error] (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF))))
      a
    -> Validation [Error] Check a
  phi env _ node = case node of
    ModuleDecl i ds ->
      case (i $$ K env, hsequence $ ($$ K env) <$> ds) of
        (i', ds') -> (\f -> hpure f <**> i' <**> ds') $
          Nat' $ \i -> Nat' $ \(Compose ds) -> Check ((), ModuleDecl i ds)
    Var i -> ident (strip i)

moduleDecl
  :: Nat'
    (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF))
    'IdentN
    (Nat'
      (Compose [] (HFix (PAnn '[TypeCheck, K SrcSpan] ASTF)))
      'TopLevelDeclN
      Check)
    'ModuleDeclN
moduleDecl = Nat' $ \i -> Nat' $ \(Compose ds) -> Check ((), ModuleDecl i ds)

  -- phi :: forall a.
  --   ASTF (
  --     Nat
  --       (K [CheckTypeScopes])
  --       (Validation
  --         (K [TypeVariableNotInScope])
  --         (HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF)))
  --   ) a
  --   -> P '[K SrcSpan] a
  --   -> Nat
  --     (K [CheckTypeScopes])
  --     (Validation
  --       (K [TypeVariableNotInScope])
  --       (HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF)))
  --     a
  -- phi node _ = case collapseIndex node of
  --   ModuleDeclS -> case node of
  --     ModuleDecl name decls -> do
  --       name' <- pushDown name
  --       decls' <- traverse pushDown decls
  --       pure ( TypeBindingSiteE (), ModuleDecl name' decls' )

  --   TopLevelDeclS -> case node of
  --     TermDecl name mty t -> do
  --       name' <- pushDown name
  --       mty' <- traverse pushDown mty
  --       t' <- pushDown t
  --       pure ( TypeBindingSiteE (), TermDecl name' mty' t' )
  --     TypeDecl decl -> do
  --       decl' <- pushDown decl
  --       pure ( TypeBindingSiteE (), TypeDecl decl' )

  --   TypeDeclS -> case node of
  --     DataDecl name tys ctors -> do
  --       name' <- pushDown name
  --       tys' <- traverse pushDown tys
  --       -- check the constructors in the new scope
  --       ctors' <- withNewBindings tys' $ traverse pushDown ctors

  --       pure ( TypeBindingSiteE (), DataDecl name' tys' ctors' )

  --     CodataDecl name tys obs -> do
  --       name' <- pushDown name
  --       tys' <- traverse pushDown tys
  --       -- check the observations in the new scope
  --       obs' <- withNewBindings tys' $ traverse pushDown obs

  --       pure ( TypeBindingSiteE (), CodataDecl name' tys' obs' )

  --   TypeS -> case node of
  --     NamedType name -> do
  --       name' <- pushDown name
  --       pure ( TypeBindingSiteE (), NamedType name' )
  --       -- need to lift the ReaderT computations into the exception monad so
  --       -- that we can throw if there are out-of-scope identifiers.

  --     ArrowType t1 t2 -> do
  --       t1' <- pushDown t1
  --       t2' <- pushDown t2
  --       pure ( TypeBindingSiteE (), ArrowType t1' t2' )

  --     ProductType t1 t2 -> do
  --       t1' <- pushDown t1
  --       t2' <- pushDown t2
  --       pure ( TypeBindingSiteE (), ProductType t1' t2' )

  --     Next t -> do
  --       t' <- pushDown t
  --       pure ( TypeBindingSiteE (), Next t' )

  --   TypeNameS -> case node of
  --     TypeName i -> do
  --       i' <- pushDown i
  --       b <- lookupTypeBinding i'
  --       pure ( TypeBindingSiteE b, TypeName i' )

  --   IdentS -> case node of
  --     Identifier t -> pure ( TypeBindingSiteE (), Identifier t )

  --   FunEquationS -> case node of
  --     FunEquation cop t -> do
  --       cop' <- pushDown cop
  --       t' <- pushDown t
  --       pure ( TypeBindingSiteE (), FunEquation cop' t' )

  --   ExprS -> case node of
  --     Fun eqs -> do
  --       eqs' <- traverse pushDown eqs
  --       pure ( TypeBindingSiteE (), Fun eqs' )

  --     App t1 t2 -> do
  --       t1' <- pushDown t1
  --       t2' <- pushDown t2
  --       pure ( TypeBindingSiteE (), App t1' t2' )

  --     Var i -> do
  --       i' <- pushDown i
  --       pure ( TypeBindingSiteE (), Var i' )

  --     ObservationExpr obs -> do
  --       obs' <- pushDown obs
  --       pure ( TypeBindingSiteE (), ObservationExpr obs' )

  --   CtorS -> case node of
  --     ConstructorDef name ty -> do
  --       name' <- pushDown name
  --       ty' <- pushDown ty
  --       pure ( TypeBindingSiteE (), ConstructorDef name' ty' )

  --   ObsS -> case node of
  --     DestructorDef name ty -> do
  --       name' <- pushDown name
  --       ty' <- pushDown ty
  --       pure ( TypeBindingSiteE (), DestructorDef name' ty' )

  --   CopatternS -> case node of
  --     EmptyCopattern -> pure ( TypeBindingSiteE (), EmptyCopattern )

  --     CopatternPattern p c -> do
  --       p' <- pushDown p
  --       c' <- pushDown c
  --       pure ( TypeBindingSiteE (), CopatternPattern p' c' )

  --     ObservationCopattern obs c -> do
  --       obs' <- pushDown obs
  --       c' <- pushDown c
  --       pure ( TypeBindingSiteE (), ObservationCopattern obs' c' )

  --   PatternS -> case node of
  --     PatternVar i -> do
  --       i' <- pushDown i
  --       pure ( TypeBindingSiteE (), PatternVar i' )

  --     PairPattern p1 p2 -> do
  --       p1' <- pushDown p1
  --       p2' <- pushDown p2
  --       pure ( TypeBindingSiteE (), PairPattern p1' p2' )

  --     ConstructorPattern i p -> do
  --       i' <- pushDown i
  --       p' <- pushDown p
  --       pure ( TypeBindingSiteE (), ConstructorPattern i' p' )

  --     UnderscorePattern -> pure ( TypeBindingSiteE (), UnderscorePattern )

  --   ObservationS -> case node of
  --     Observation i -> do
  --       i' <- pushDown i
  --       pure ( TypeBindingSiteE (), Observation i' )

-- | Converts a topdown traversal with invariant inputs into a reader
-- computation whose @K@ functor is polymorphic, allowing it to be used
-- anywhere.
pushDown :: TopDownHT (K x) m f a -> ReaderT (K x b) m (f a)
pushDown = withReaderT repackage . toReaderT

-- -- | The key is the identifier for the type and the value is the binding
-- -- distance.
-- --
-- -- e.g. in @data Foo a b c = A a | B b | C c@ we say @a@, @b@, and @c@ have
-- -- distances 2, 1, and 0 respectively in the body of the declaration.
-- --
-- -- If the binder is outside (it's the name of another datatype in the file)
-- -- then we use the 'TyBoundOutside' constructor.
-- --
-- -- The value also includes the source position where the binder was introduced.
-- type CheckTypeScopes = M.Map Text (SrcSpan, TypeBinding)

-- -- | Processes the given reader computation in a modified environment where new
-- -- type bindings have been introduced.
-- withNewBindings
--   :: forall (a :: k) (b :: *) (m :: * -> *).
--     [HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF) 'IdentN]
--   -> ReaderT (K CheckTypeScopes a) m b
--   -> ReaderT (K CheckTypeScopes a) m b
-- withNewBindings tys m = do
--   -- enumerate the bound variables
--   let rtys = reverse tys
--   let etys = zip [0..] $ rtys
--   let tyNames = ident . stripAnn <$> rtys
--   -- construct the bindings
--   let binders = mkTypeBinding <$> etys
--   -- construct the new scope (as a function that transforms the current
--   -- scope)
--   let newScope = kmap (M.union (M.fromList (zip tyNames binders)))
--   local newScope m
--
-- mkTypeBinding
--   :: (Int, HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF) 'IdentN)
--   -> (SrcSpan, TypeBinding)
-- mkTypeBinding (i, HFix (IAnn ps (Identifier _))) =
--   (unK (getH Proxy ps), TypeBound i)
--
-- -- | Look up the given type name in the context.
-- lookupTypeBinding
--   :: (Monad m, MonadError m, Error m ~ TreeError TypeVariableNotInScope)
--   => HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF) 'IdentN
--   -> ReaderT (K CheckTypeScopes a) m (Either TypeVariableNotInScope TypeBinding)
-- lookupTypeBinding (HFix (IAnn _ (Identifier name))) = do
--   asks (M.lookup name . unK) >>= \case
--     Nothing -> do
--       ctx <- asks unK
--       pure $ Left TypeVariableNotInScope
--         { tvScopeName = name
--         , tvInScope = ctx
--         }
--     Just (_, x) -> pure (Right x)

-- checkTypeScopesTree
--   :: forall n node.
--     (MonadError n, Monad n, Error n ~ TreeError

-- typecheck
--   :: forall node. HFix (IAnn (P '[K SrcSpan]) ASTF) node
--   -> HFix (IAnn (P '[Typing, K SrcSpan]) ASTF) node
-- typecheck = hcata (HFix . consAnnotate phi) where
--   phi
--     :: forall n. ASTF (HFix (IAnn (P '[Typing, K SrcSpan]) ASTF)) n
--     -> P '[K SrcSpan] n
--     -> Typing n
--   phi node (PCons a PNil) = _
