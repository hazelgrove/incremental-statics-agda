
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core

module Core.VariableUpdate where

  data VariableUpdate : Var -> Type -> Mark -> SynExp -> SynExp -> Set where 
    VSConst : ∀ {x m t syn} ->
      VariableUpdate x t m (EConst ⇒ syn) (EConst ⇒ syn)
    VSHole : ∀ {x m t syn} ->
      VariableUpdate x t m (EHole ⇒ syn) (EHole ⇒ syn)
    VSFunEq : ∀ {x m t asc m-ana m-asc e-body m-body syn-all ana-body} ->
      VariableUpdate x t m ((EFun (BVar x) asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun (BVar x) asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all)
    VSFunNeq : ∀ {x m x' t asc m-ana m-asc e-body e-body' m-body syn-all ana-body} ->
      ¬((BVar x) ≡ x') ->
      VariableUpdate x t m e-body e-body' ->
      VariableUpdate x t m ((EFun x' asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun x' asc m-ana m-asc (e-body' [ m-body ]⇐ ana-body)) ⇒ syn-all)
    VSAp : ∀ {x m t syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
      VariableUpdate x t m e1 e1' ->
      VariableUpdate x t m e2 e2' ->
      VariableUpdate x t m ((EAp (e1 [ m1 ]⇐ ana1) m2 (e2 [ m3 ]⇐ ana2)) ⇒ syn) ((EAp (e1' [ m1 ]⇐ ana1) m2 (e2' [ m3 ]⇐ ana2)) ⇒ syn)
    VSVarEq : ∀ {x m m' t syn} ->
      VariableUpdate x t m ((EVar x m') ⇒ syn) ((EVar x m) ⇒ ((■ t , ★)))
    VSVarNeq : ∀ {x m x' t m' syn} ->
      ¬(x ≡ x') -> 
      VariableUpdate x t m ((EVar x' m') ⇒ syn) ((EVar x' m') ⇒ syn)
    VSAsc : ∀ {x m t syn asc e e' ana m'} ->
      VariableUpdate x t m e e' ->
      VariableUpdate x t m ((EAsc asc (e [ m' ]⇐ ana)) ⇒ syn) ((EAsc asc (e' [ m' ]⇐ ana)) ⇒ syn)
    VSPair : ∀ {x m t syn e1 e1' e2 e2' ana1 ana2 m1 m2 m'} ->
      VariableUpdate x t m e1 e1' ->
      VariableUpdate x t m e2 e2' ->
      VariableUpdate x t m ((EPair (e1 [ m1 ]⇐ ana1) (e2 [ m2 ]⇐ ana2) m') ⇒ syn) ((EPair (e1' [ m1 ]⇐ ana1) (e2' [ m2 ]⇐ ana2) m') ⇒ syn) 
    VSProj : ∀ {x s m t syn e e' ana m' m''} ->
      VariableUpdate x t m e e' ->
      VariableUpdate x t m ((EProj s (e [ m' ]⇐ ana) m'') ⇒ syn) ((EProj s (e' [ m' ]⇐ ana) m'') ⇒ syn) 

  VariableUpdate? : Binding -> Type -> Mark -> SynExp -> SynExp -> Set
  VariableUpdate? BHole t m e1 e2 = e1 ≡ e2
  VariableUpdate? (BVar x) t m e1 e2 = VariableUpdate x t m e1 e2