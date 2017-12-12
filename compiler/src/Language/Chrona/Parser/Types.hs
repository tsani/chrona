module Language.Chrona.Parser.Types where

import Data.Annotation
import Data.HFunctor
import Language.Chrona.Types

import Text.Megaparsec ( SourcePos(..) )

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

-- | Combine two spans into a span that spans both spans.
--
-- Warning: the spans must be given in order, and this operation does not
-- validate the resulting span (start must come before end)
joinSpan :: SrcSpan -> SrcSpan -> SrcSpan
joinSpan (SrcSpan start _) (SrcSpan _ end) = SrcSpan start end

-- | Checks whether a span is valid:
-- the start position must come before the end position, and the start and end
-- must be within the same file.
validSpan :: SrcSpan -> Bool
validSpan (SrcSpan (SourcePos name1 line1 col1) (SourcePos name2 line2 col2)) =
  name1 == name2 && (line1, col1) <= (line2, col2)
  -- take advantage of the fact that tuples are compared lexicographically
