module Universe

%access public export
%default total

data TYPE = Nat | Bool | Function TYPE TYPE

||| Decides whether a type is a function type.
isFunction : (ty : TYPE) ->
             Dec (p : (TYPE, TYPE) ** (ty = Function (fst p) (snd p)))
isFunction Nat = No $ \(_ ** Refl) impossible
isFunction Bool = No $ \(_ ** Refl) impossible
isFunction (Function s t) = Yes ((s, t) ** Refl)

DecEq TYPE where
  decEq Nat Nat = Yes Refl
  decEq Nat Bool = No $ \Refl impossible
  decEq Nat (Function _ _) = No $ \Refl impossible
  decEq Bool Nat = No $ \Refl impossible
  decEq Bool Bool = Yes Refl
  decEq Bool (Function _ _) = No $ \Refl impossible
  decEq (Function _ _) Nat = No $ \Refl impossible
  decEq (Function _ _) Bool = No $ \Refl impossible
  decEq (Function s1 t1) (Function s2 t2) =
    case (decEq s1 s2, decEq t1 t2) of
         (Yes Refl, Yes Refl) => Yes Refl
         (Yes Refl, No contra) => No $ \Refl => contra Refl
         (No contra, Yes Refl) => No $ \p => case p of Refl => contra Refl
         (No contra, No _) => No $ \p => case p of Refl => contra Refl
