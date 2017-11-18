module Language.Chrona.Parser.Types where

import Data.Annotation
import Data.HFunctor
import Data.HFunctor.Basic
import Language.Chrona.Types

import Text.Megaparsec ( SourcePos )

-- | A source AST is uniformly annotated with source spans.
type SrcAnnF = IAnn (K SrcSpan)
type SrcASTF = SrcAnnF ASTF
type SrcAST = HFix (IAnn (K SrcSpan) ASTF)

-- | A source span has a beginning and an end that refer to locations in a
-- source file.
data SrcSpan
    = SrcSpan
        { srcStart :: !SourcePos
        , srcEnd :: !SourcePos
        }
    deriving (Eq, Ord, Show)

