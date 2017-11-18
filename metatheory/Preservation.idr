module Preservation

import Context
import Eval
import EvalContext
import Term
import Typing
import Value
import Universe

evalPreservesTyping : EvalContextFor ectx ctx ->
                      WellTyped ctx t ty ->
                      Eval ectx t t' ->
                      WellTyped ctx t' ty
evalPreservesTyping ectxf w (Var vectx ee) =
  case w of
       Var vctx ety =>
         let w = lookupBoth ety ee vctx vectx ectxf in ?z
