{-|
Module      : Language.Chrona.Monad.Types
Description : Monad classes for effectful traversals.
Copyright   : (c) Jacob Errington 2017
License     : MIT
Maintainer  : chrona@mail.jerrington.me
Stability   : experimental

This module describes several monad classes that provide common effects that
are necessary when processing a syntax tree, such as reporting warnings,
errors, and aborting.
-}
module Language.Chrona.Monad.Types where

import Data.Reflection

data Severity
  = WarningN
  -- ^ An error that still results in code that can be executed, but may have
  -- unintended semantics.
  | ErrorN
  -- ^ An error that results in code that cannot be executed, but that does not
  -- impede further compilation.
  | FatalN
  -- ^ An error that results in code that connect be executed and impedes
  -- further compilation.
  | InternalN
  -- ^ An error that arises due to the violation of an internal invariant.
  -- These errors are compiler bugs.

-- | Singletons for the 'Severity' kind.
data SeverityS (s :: Severity) :: * where
  WarningS :: SeverityS 'WarningN
  ErrorS :: SeverityS 'ErrorN
  FatalS :: SeverityS 'FatalN
  InternalS :: SeverityS 'InternalN

deriving instance Eq (SeverityS n)

instance PolyEq SeverityS where
  peq s1 s2 = case (s1, s2) of
    (WarningS, WarningS) -> True
    (ErrorS, ErrorS) -> True
    (FatalS, FatalS) -> True
    (InternalS, InternalS) -> True
    _ -> False

-- connect the datakind with its reification
type instance Demote Severity = SeverityS

instance Reflect 'WarningN where reflect _ = WarningS
instance Reflect 'ErrorN where reflect _ = ErrorS
instance Reflect 'FatalN where reflect _ = FatalS
instance Reflect 'InternalN where reflect _ = InternalS

-- -- can't figure out how to get this to typecheck just yet
-- instance Forget SeverityS where
--   forget WarningS = Some Proxy

-- | A monad representing errors (and warnings).
class MonadError m where
  -- | The type of errors used by the monad.
  type Error m :: Severity -> *

  -- | Signals an error.
  --
  -- Conforming implementations of this class should respect the index @s@ and
  -- continue / abort processing accordingly.
  reportError :: Error m s -> m ()
