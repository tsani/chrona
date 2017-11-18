module Language.Chrona.Monad.Error where

import Language.Chrona.Monad.Types
import Language.Chrona.Parser.Types ( SrcSpan )

data ErrorLoc = LocUnknown | Loc SrcSpan
  deriving (Eq, Ord)

data TreeError a s =
  TreeError
    { location :: ErrorLoc
    , severity :: SeverityS s
    , contents :: a
    }

instance Eq a => Eq (TreeError a s) where
  (==) (TreeError l1 p1 m1) (TreeError l2 p2 m2) =
    l1 == l2 && p1 == p2 && m1 == m2 where
