open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.Lemmas-Context where

  ctx-unique : ∀ {A} -> ∀ {Γ : Context A} -> ∀ {t1 t2 x} -> 
    (x , t1 ∈ Γ) ->
    (x , t2 ∈ Γ) ->
    t1 ≡ t2 
  ctx-unique {Γ = ∅} () () 
  ctx-unique {Γ = x , Γ} InCtx0 InCtx0 = refl
  ctx-unique {Γ = x , Γ} (InCtxSuc in1) (InCtxSuc in2) = ctx-unique in1 in2