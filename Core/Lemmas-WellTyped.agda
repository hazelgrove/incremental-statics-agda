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
open import Core.WellTyped
open import Core.Lemmas-Context 

module Core.Lemmas-WellTyped where

  ▸TArrow-unicity : 
    ∀ {t t1 t2 t3 t4} ->
    t ▸TArrow t1 , t2 ->
    t ▸TArrow t3 , t4 ->
    (t1 ≡ t3) × (t2 ≡ t4)
  ▸TArrow-unicity MArrowHole MArrowHole = refl , refl
  ▸TArrow-unicity MArrowArrow MArrowArrow = refl , refl

  ▸NArrow-unicity : 
    ∀ {n n1 n2 n3 n4} ->
    n ▸NArrow n1 , n2 ->
    n ▸NArrow n3 , n4 ->
    (n1 ≡ n3) × (n2 ≡ n4)
  ▸NArrow-unicity MNArrowOld MNArrowOld = refl , refl
  ▸NArrow-unicity MNArrowNew MNArrowNew = refl , refl
  ▸NArrow-unicity MNArrowArrow MNArrowArrow = refl , refl

  merge-unicity : 
    ∀ {i1 i2 i3 i4} ->
    MergeInfo i1 i2 i3 ->
    MergeInfo i1 i2 i4 ->
    i3 ≡ i4
  merge-unicity MergeInfoNew MergeInfoNew = refl
  merge-unicity MergeInfoOld MergeInfoOld = refl
  merge-unicity (MergeInfoArrow mn1 m1 m2 refl) (MergeInfoArrow mn2 m3 m4 refl) with ▸NArrow-unicity mn1 mn2 
  ... | refl , refl with merge-unicity m1 m3 | merge-unicity m2 m4 
  ... | refl | refl = refl

  oldify-merge : 
    ∀ {t1 t2 t3 n1 n2 n3} ->
    MergeInfo (t1 , n1) (t2 , n2) (t3 , n3) ->
    ∃[ n4 ] MergeInfo (t1 , Old) (t2 , n2) (t3 , n4)
  oldify-merge MergeInfoNew = New , MergeInfoNew
  oldify-merge MergeInfoOld = Old , MergeInfoOld
  oldify-merge (MergeInfoArrow x m1 m2 x₁) with oldify-merge m1 | oldify-merge m2 
  ... | n1 , m1' | n2 , m2' = narrow n1 n2 , MergeInfoArrow MNArrowOld m1' m2' refl
  
  merge-same : 
    ∀ {t1 t2 t3 n1 n2 n3} ->
    MergeInfo (t1 , n1) (t2 , n2) (t3 , n3) -> 
    t2 ≡ t3
  merge-same MergeInfoNew = refl
  merge-same MergeInfoOld = refl
  merge-same (MergeInfoArrow x m m₁ x₁) rewrite (merge-same m) rewrite (merge-same m₁) = refl

  syn-unicity : 
    ∀ {Γ e t1 t2} ->
    Γ ⊢ e ⇒ t1 ->
    Γ ⊢ e ⇒ t2 ->
    t1 ≡ t2
  syn-unicity (SynConst m1) (SynConst m2) = merge-unicity m1 m2
  syn-unicity (SynHole m1) (SynHole m2) = merge-unicity m1 m2
  syn-unicity (SynFun syn1 refl m1) (SynFun syn2 refl m2) with syn-unicity syn1 syn2 
  ... | refl = merge-unicity m1 m2
  syn-unicity (SynFunVoid syn1) (SynFunVoid syn2) with syn-unicity syn1 syn2 
  ... | refl = refl
  syn-unicity (SynAp syn1 mt1 mn1 ana1 m1) (SynAp syn2 mt2 mn2 ana2 m2) with syn-unicity syn1 syn2 
  ... | refl with ▸TArrow-unicity mt1 mt2 | ▸NArrow-unicity mn1 mn2 
  ... | refl , refl | refl , refl = merge-unicity m1 m2
  syn-unicity (SynApFail syn1 mt1 mn1 ana1 m1) (SynApFail syn2 mt2 mn2 ana2 m2) with syn-unicity syn1 syn2 
  ... | refl with ▸NArrow-unicity mn1 mn2 
  ... | refl , refl = merge-unicity m1 m2
  syn-unicity (SynVar inctx1 m1) (SynVar inctx2 m2) rewrite (ctx-unicity inctx1 inctx2) = merge-unicity m1 m2
  syn-unicity (SynVarFail _ m1) (SynVarFail _ m2) = merge-unicity m1 m2
  syn-unicity (SynAsc _ m1) (SynAsc _ m2) = merge-unicity m1 m2