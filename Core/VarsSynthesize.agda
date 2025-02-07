open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment
open import Core.WellTyped

module Core.VarsSynthesize where

  data VarsSynthesize : Var -> Type -> ExpUp -> ExpUp -> Set where 
    VSConst : ∀ {x t syn} ->
      VarsSynthesize x t (EConst ⇒ syn) (EConst ⇒ syn)
    VSHole : ∀ {x t syn} ->
      VarsSynthesize x t (EHole ⇒ syn) (EHole ⇒ syn)
    VSFunEq : ∀ {x t asc m-ana m-asc e-body m-body syn-all ana-body} ->
      VarsSynthesize x t ((EFun (BVar x) asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun (BVar x) asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all)
    VSFunNeq : ∀ {x x' t asc m-ana m-asc e-body e-body' m-body syn-all ana-body} ->
      ¬((BVar x) ≡ x') ->
      VarsSynthesize x t e-body e-body' ->
      VarsSynthesize x t ((EFun x' asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun x' asc m-ana m-asc (e-body' [ m-body ]⇐ ana-body)) ⇒ syn-all)
    VSAp : ∀ {x t syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
      VarsSynthesize x t e1 e1' ->
      VarsSynthesize x t e2 e2' ->
      VarsSynthesize x t ((EAp (e1 [ m1 ]⇐ ana1) m2 (e2 [ m3 ]⇐ ana2)) ⇒ syn) ((EAp (e1' [ m1 ]⇐ ana1) m2 (e2' [ m3 ]⇐ ana2)) ⇒ syn)
    VSVarEq : ∀ {x m t syn} ->
      VarsSynthesize x t ((EVar x m) ⇒ syn) ((EVar x ✔) ⇒ ((■ t , New)))
    VSVarNeq : ∀ {x x' t m syn} ->
      ¬(x ≡ x') -> 
      VarsSynthesize x t ((EVar x' m) ⇒ syn) ((EVar x' m) ⇒ syn)
    VSAsc : ∀ {x t syn asc e e' ana m} ->
      VarsSynthesize x t e e' ->
      VarsSynthesize x t ((EAsc asc (e [ m ]⇐ ana)) ⇒ syn) ((EAsc asc (e' [ m ]⇐ ana)) ⇒ syn)

  VarsSynthesize? : Binding -> Type -> ExpUp -> ExpUp -> Set
  VarsSynthesize? BHole t e1 e2 = e1 ≡ e2
  VarsSynthesize? (BVar x) t e1 e2 = VarsSynthesize x t e1 e2