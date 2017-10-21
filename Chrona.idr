module Chrona

import Context
import Eval
import EvalContext
import Misc
import Preservation
import Progress
import Term
import Typecheck
import Typing
import Value
import Weakening

%default total
%access public export

-- codata EvalTrace : (lbl : Type) -> Term lbl TYPE -> Type where
--   Terminated : (t : Term lbl TYPE) ->
--                IsValue t ->
--                EvalTrace lbl t
--   Step : WellTyped ctx t ty {lbl} ->
--          Eval ectx t t' ->
--          EvalTrace lbl t' ->
--          EvalTrace lbl t
-- 
-- evaluate : DecEq lbl => WellTyped Nil t ty {lbl} -> EvalTrace lbl t
-- evaluate w = go w Nil where
--   go : DecEq lbl =>
--        WellTyped ctx t ty {lbl} ->
--        EvalContextFor ectx ctx ->
--        EvalTrace lbl t
--   go w ectxf =
--     case progress w ectxf of
--          Left v => Terminated _ v
--          Right (t ** ectx' ** ev) => ?z
--            -- let w' = evalPreservesTyping ?b w ev in ?z
