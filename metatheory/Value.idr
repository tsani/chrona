module Value

import Term

%default total
%access public export

||| Proof that something is a value.
data IsValue : (t : Term var ty) -> Type where
  Zero : IsValue Zero
  Succ : IsValue t -> IsValue (Succ t)
  True : IsValue True
  False : IsValue False
  Abstract : IsValue {var} (Abstract param ty body)

||| A value is a term that is known to be a value. Duh.
Value : Type -> Type -> Type
Value var ty = (t : Term var ty ** IsValue t)

Uninhabited (IsValue (Var l)) where
  uninhabited x =
    case x of
         Zero impossible
         (Succ _) impossible
         True impossible
         False impossible
         Abstract impossible

Uninhabited (IsValue (Pred t)) where
  uninhabited x =
    case x of
         Zero impossible
         (Succ _) impossible
         True impossible
         False impossible
         Abstract impossible

Uninhabited (IsValue (Apply f x)) where
  uninhabited x =
    case x of
         Zero impossible
         (Succ _) impossible
         True impossible
         False impossible
         Abstract impossible

Uninhabited (IsValue (IfThenElse cond true false)) where
  uninhabited x =
    case x of
         Zero impossible
         (Succ _) impossible
         True impossible
         False impossible
         Abstract impossible

||| Decides whether a given term is a value.
decValue : (v : Term var ty) -> Dec (IsValue v)
decValue Zero = Yes Zero
decValue (Succ t) = case decValue t of
                         Yes prf => Yes (Succ prf)
                         No contra => No $ \v =>
                           case v of Succ prf => contra prf
decValue True = Yes True
decValue False = Yes False
decValue (Pred _) = No uninhabited
decValue (IfThenElse _ _ _) = No uninhabited
decValue (Apply _ _) = No uninhabited
decValue (Abstract _ _ _) = Yes Abstract
decValue (Var _) = No uninhabited
