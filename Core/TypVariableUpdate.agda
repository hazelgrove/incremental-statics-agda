
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core

module Core.TypVariableUpdate where

  data TypVariableUpdate : Var -> Mark -> Type -> Type -> Set where 
    TVUBase : ∀ {x m} ->
      TypVariableUpdate x m TBase TBase
    TVUHole : ∀ {x m} ->
      TypVariableUpdate x m THole THole
    TVUArrow : ∀ {x m t1 t2 t3 t4} ->
      TypVariableUpdate x m t1 t3 ->
      TypVariableUpdate x m t2 t4 ->
      TypVariableUpdate x m (TArrow t1 t2) (TArrow t3 t4)
    TVUProd : ∀ {x m t1 t2 t3 t4} ->
      TypVariableUpdate x m t1 t3 ->
      TypVariableUpdate x m t2 t4 ->
      TypVariableUpdate x m (TProd t1 t2) (TProd t3 t4)
    TVUVarEq : ∀ {x m m'} ->
      TypVariableUpdate x m (TVar x m') (TVar x m)
    TVUVarNeq : ∀ {x m x' m'} ->
      ¬(x ≡ x') -> 
      TypVariableUpdate x m (TVar x' m') (TVar x' m')
    TVUForallEq : ∀ {x m t} ->
      TypVariableUpdate x m (TForall (BVar x) t) (TForall (BVar x) t)
    TVUForallNeq : ∀ {x m x' t t'} ->
      ¬((BVar x) ≡ x') ->
      TypVariableUpdate x m t t' ->
      TypVariableUpdate x m (TForall x' t) (TForall x' t')
    
  TypVariableUpdate? : Binding -> Mark -> Type -> Type -> Set
  TypVariableUpdate? BHole m t1 t2 = t1 ≡ t2
  TypVariableUpdate? (BVar x) m t1 t2 = TypVariableUpdate x m t1 t2