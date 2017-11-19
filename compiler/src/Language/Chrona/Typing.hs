module Language.Chrona.Typing where

import Data.Maybe ( catMaybes )
import qualified Data.Map as M
import Data.Text ( Text )

import Language.Chrona.Types
import Language.Chrona.Parser.Types
import Language.Chrona.Monad
import Data.Annotation
import Data.HFunctor
import Data.HFunctor.Basic
import Data.HFunctor.TopDown

type family Typing' (node :: Node) :: * where

newtype Typing (node :: Node)
  = Typing
    { typing :: Typing' node
    }

-- we need to collect all type declarations so we know whether a named type
-- refers to a defined type or is a type variable.

-- first we collect the names of all types declared in the module

type family CollectTypes' (node :: Node) :: * where
  CollectTypes' 'TopLevelDeclN = Maybe Text
  CollectTypes' 'TypeDeclN = Text
  CollectTypes' 'ModuleDeclN = [Text]
  CollectTypes' 'IdentN = Text
  CollectTypes' a = ()

newtype CollectTypes (node :: Node)
  = CollectTypes
    { collectedTypes :: CollectTypes' node
    }

collectTypes
  :: forall node. HFix ASTF node
  -> CollectTypes node
collectTypes = hcata phi where
  phi :: forall n. ASTF CollectTypes n -> CollectTypes n
  phi node = case collapseIndex node of
    ModuleDeclS -> case node of
      ModuleDecl _ ts -> CollectTypes $ catMaybes $ collectedTypes <$> ts
    TopLevelDeclS -> case node of
      TypeDecl (CollectTypes n) -> CollectTypes (Just n)
      TermDecl _ _ _ -> CollectTypes Nothing
    TypeDeclS -> case node of
      DataDecl (CollectTypes n) _ _ -> CollectTypes n
      CodataDecl (CollectTypes n) _ _ -> CollectTypes n
    IdentS -> case node of
      Identifier t -> CollectTypes t

    -- feels bad
    FunEquationS -> CollectTypes ()
    ExprS -> CollectTypes ()
    TypeS -> CollectTypes ()
    CtorS -> CollectTypes ()
    FieldS -> CollectTypes ()
    ObsS -> CollectTypes ()
    PatternS -> CollectTypes ()
    CopatternS -> CollectTypes ()
    ObservationS -> CollectTypes ()
    TypeNameS -> CollectTypes ()

-- next we need to check all type names for scoping issues.
-- we annotate each occurrence of NamedType with how the name is bound: either
-- to a type variable or to another type.
-- We use a de Bruijn style representation here: we annotate bound namedtypes
-- with their index into the list and "free" namedtypes are marked
-- free

-- | The binding information of a type: either a type is free (refers to
-- another datatype in the file) or is bound (refers to a type variable
-- introduced by the (co)data declaration).
data TypeBinding = TypeFree | TypeBound Int

-- | Annotation function for type bindings. Only type names are annotated by
-- this annotation.
type family TypeBindingSiteE' (node :: Node) :: * where
  TypeBindingSiteE' 'TypeNameN = Either TypeVariableNotInScope TypeBinding
  TypeBindingSiteE' _ = ()

-- | Represents the type family 'TypeBindingSiteE''.
newtype TypeBindingSiteE (node :: Node)
  = TypeBindingSiteE
    { bindingSite :: TypeBindingSiteE' node
    }

-- | The key is the identifier for the type and the value is the binding
-- distance.
--
-- e.g. in @data Foo a b c = A a | B b | C c@ we say @a@, @b@, and @c@ have
-- distances 2, 1, and 0 respectively in the body of the declaration.
--
-- If the binder is outside (it's the name of another datatype in the file)
-- then we use the 'TyBoundOutside' constructor.
--
-- The value also includes the source position where the binder was introduced.
type CheckTypeScopes = M.Map Text (SrcSpan, TypeBinding)

-- to pull off this traversal we need to have some information coming in /from
-- above/: if we enter a type from a function declaration, then free variables
-- are all implicitly bound if they don't refer to an external type; whereas if
-- we enter a type from a (co)data declaration then free variables are simply
-- not permitted. In that case we have to add the bindings introduced by the
-- declaration to the scoping map.
checkTypeScopesTree
  :: forall n node. (MonadError n, Monad n, Error n ~ TreeError TypeVariableNotInScope)
  => HFix (PAnn '[K SrcSpan] ASTF) node
  ->
    TopDownHT
      (K CheckTypeScopes)
      n
      (HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF))
      node
checkTypeScopesTree = hcata (hfmap HFix . topDownConsAnnotate phi) where
  phi :: forall b.
    ASTF (
      TopDownHT
        (K CheckTypeScopes)
        n
        (HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF))
    ) b
    -> P '[K SrcSpan] b
    ->
      ReaderT
        (K CheckTypeScopes b)
        n
        (TypeBindingSiteE b, ASTF (HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF)) b)
  phi node _ = case collapseIndex node of
    ModuleDeclS -> case node of
      ModuleDecl name decls -> do
        name' <- pushDown name
        decls' <- traverse pushDown decls
        pure ( TypeBindingSiteE (), ModuleDecl name' decls' )

    TopLevelDeclS -> case node of
      TermDecl name mty t -> do
        name' <- pushDown name
        mty' <- traverse pushDown mty
        t' <- pushDown t
        pure ( TypeBindingSiteE (), TermDecl name' mty' t' )
      TypeDecl decl -> do
        decl' <- pushDown decl
        pure ( TypeBindingSiteE (), TypeDecl decl' )

    TypeDeclS -> case node of
      DataDecl name tys ctors -> do
        name' <- pushDown name
        tys' <- traverse pushDown tys
        -- check the constructors in the new scope
        ctors' <- withNewBindings tys' $ traverse pushDown ctors

        pure ( TypeBindingSiteE (), DataDecl name' tys' ctors' )

      CodataDecl name tys obs -> do
        name' <- pushDown name
        tys' <- traverse pushDown tys'
        -- check the observations in the new scope
        obs' <- withNewBindings tys' $ traverse pushDown obs

        pure ( TypeBindingSiteE (), CodataDecl name' tys' obs' )

    TypeS -> case node of
      NamedType name -> do
        name' <- withReaderT repackage $ toReaderT name
        pure ( TypeBindingSiteE (), NamedType name' )
        -- need to lift the ReaderT computations into the exception monad so
        -- that we can throw if there are out-of-scope identifiers.

    TypeNameS -> case node of
      TypeName i -> do
        i' <- withReaderT repackage $ toReaderT i
        b <- lookupTypeBinding i'
        pure ( TypeBindingSiteE b, TypeName i' )

-- | Converts a topdown traversal with invariant inputs into a reader
-- computation whose @K@ functor is polymorphic, allowing it to be used
-- anywhere.
pushDown :: TopDownHT (K x) m f a -> ReaderT (K x b) m (f a)
pushDown = withReaderT repackage . toReaderT

-- | Processes the given reader computation in a modified environment where new
-- type bindings have been introduced.
withNewBindings
  :: forall (a :: k) (b :: *) (m :: * -> *).
    [HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF) 'IdentN]
  -> ReaderT (K CheckTypeScopes a) m b
  -> ReaderT (K CheckTypeScopes a) m b
withNewBindings tys m = do
  -- enumerate the bound variables
  let rtys = reverse tys
  let etys = zip [0..] $ rtys
  let tyNames = ident . stripAnn <$> rtys
  -- construct the bindings
  let binders = mkTypeBinding <$> etys
  -- construct the new scope (as a function that transforms the current
  -- scope)
  let newScope = kmap (M.union (M.fromList (zip tyNames binders)))
  local newScope m

mkTypeBinding
  :: (Int, HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF) 'IdentN)
  -> (SrcSpan, TypeBinding)
mkTypeBinding (i, HFix (IAnn ps (Identifier t))) =
  (unK (getH Proxy ps), TypeBound i)

data TypeVariableNotInScope
  = TypeVariableNotInScope
    { tvScopeName :: Text
    , tvInScope :: CheckTypeScopes
    }

-- | Look up the given type name in the context.
lookupTypeBinding
  :: (Monad m, MonadError m, Error m ~ TreeError TypeVariableNotInScope)
  => HFix (PAnn '[TypeBindingSiteE, K SrcSpan] ASTF) 'IdentN
  -> ReaderT (K CheckTypeScopes a) m (Either TypeVariableNotInScope TypeBinding)
lookupTypeBinding (HFix (IAnn ps (Identifier name))) = do
  asks (M.lookup name . unK) >>= \case
    Nothing -> do
      ctx <- asks unK
      pure $ Left TypeVariableNotInScope
        { tvScopeName = name
        , tvInScope = ctx
        }
    Just (_, x) -> pure (Right x)

-- typecheck
--   :: forall node. HFix (IAnn (P '[K SrcSpan]) ASTF) node
--   -> HFix (IAnn (P '[Typing, K SrcSpan]) ASTF) node
-- typecheck = hcata (HFix . consAnnotate phi) where
--   phi
--     :: forall n. ASTF (HFix (IAnn (P '[Typing, K SrcSpan]) ASTF)) n
--     -> P '[K SrcSpan] n
--     -> Typing n
--   phi node (PCons a PNil) = _
