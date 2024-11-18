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
    i1 ▷ i2 == i3 ->
    i1 ▷ i2 == i4 ->
    i3 ≡ i4
  merge-unicity MergeInfoNew MergeInfoNew = refl
  merge-unicity MergeInfoOld MergeInfoOld = refl
  merge-unicity (MergeInfoArrow mn1 m1 m2 refl) (MergeInfoArrow mn2 m3 m4 refl) with ▸NArrow-unicity mn1 mn2 
  ... | refl , refl with merge-unicity m1 m3 | merge-unicity m2 m4 
  ... | refl | refl = refl

  merge-syn-unicity : 
    ∀ {i1 i2 i3 i4} ->
    MergeSyn i1 i2 i3 ->
    MergeSyn i1 i2 i4 ->
    i3 ≡ i4
  merge-syn-unicity MergeSynVoid MergeSynVoid = refl
  merge-syn-unicity (MergeSynMerge m1) (MergeSynMerge m2) = merge-unicity m1 m2

  merge-ana-unicity : 
    ∀ {i1 i2 i3 i4} ->
    MergeAna i1 i2 i3 ->
    MergeAna i1 i2 i4 ->
    i3 ≡ i4
  merge-ana-unicity MergeAnaVoid MergeAnaVoid = refl
  merge-ana-unicity (MergeAnaMerge m1) (MergeAnaMerge m2) = merge-unicity m1 m2

  -- oldify-merge : 
  --   ∀ {t1 t2 t3 n1 n2 n3} ->
  --   MergeInfo (t1 , n1) (t2 , n2) (t3 , n3) ->
  --   ∃[ n4 ] MergeInfo (t1 , Old) (t2 , n2) (t3 , n4)
  -- oldify-merge MergeInfoNew = New , MergeInfoNew
  -- oldify-merge MergeInfoOld = Old , MergeInfoOld
  -- oldify-merge (MergeInfoArrow x m1 m2 x₁) with oldify-merge m1 | oldify-merge m2 
  -- ... | n1 , m1' | n2 , m2' = narrow n1 n2 , MergeInfoArrow MNArrowOld m1' m2' refl

  merge-same : 
    ∀ {t1 t2 t3 n1 n2 n3} ->
    (t1 , n1) ▷ (t2 , n2) == (t3 , n3) -> 
    t1 ≡ t3
  merge-same MergeInfoNew = refl
  merge-same MergeInfoOld = refl
  merge-same (MergeInfoArrow x m m₁ x₁) rewrite (merge-same m) rewrite (merge-same m₁) = refl

  merge-lemma-fun-syn : ∀ {t t2 n2 ti1 ni1 t1 n1 info final ti2} ->
    t ▷ (t2 , n2) == (ti1 , ni1) ->
    (TArrow t1 ti1 , narrow n1 ni1) ▷ info == final -> 
    (TArrow t1 t2 , narrow Old ni1) ▷ info == ti2 -> 
    ∃[ ti3 ] ∃[ ni3 ] (t ▷ (t2 , Old) == (ti3 , ni3) × (TArrow t1 ti3 , narrow n1 ni3) ▷ ti2 == final)
  merge-lemma-fun-syn m1 m2 m3 = {! m1 m2 m3  !}

  -- merge-assoc : ∀ {t1 t2 t3 t12 t123} ->
  --   t1 ▷ t2 == t12 ->
  --   t12 ▷ t3 == t123 ->
  --   ∃[ t23 ] (t2 ▷ t3 == t23 × t1 ▷ t23 == t123)
  -- merge-assoc MergeInfoNew MergeInfoNew = {!   !} , {!   !} , {!   !}
  -- merge-assoc MergeInfoOld MergeInfoNew = {!   !}
  -- merge-assoc MergeInfoOld MergeInfoOld = {!   !}
  -- merge-assoc MergeInfoOld (MergeInfoArrow x m2 m3 x₁) = {!   !}
  -- merge-assoc (MergeInfoArrow x m1 m2 x₁) MergeInfoNew = {!   !}
  -- merge-assoc (MergeInfoArrow x m1 m2 x₁) MergeInfoOld = {!   !}
  -- merge-assoc (MergeInfoArrow x m1 m2 x₁) (MergeInfoArrow x₂ m3 m4 x₃) = {!   !}

  -- merge-assoc MergeInfoNew MergeInfoNew = (_ , New) , MergeInfoNew , MergeInfoNew
  -- merge-assoc MergeInfoNew MergeInfoOld = (_ , New) , MergeInfoOld , MergeInfoNew
  -- merge-assoc MergeInfoNew (MergeInfoArrow MNArrowNew m2 m3 refl) = {!   !} , {!   !} , {!   !}
  -- merge-assoc MergeInfoOld MergeInfoNew = (_ , New) , MergeInfoNew , MergeInfoNew
  -- merge-assoc MergeInfoOld MergeInfoOld = (_ , Old) , MergeInfoOld , MergeInfoOld
  -- merge-assoc MergeInfoOld (MergeInfoArrow x m2 m3 x₁) = {!   !}
  -- merge-assoc (MergeInfoArrow x m1 m2 x₁) MergeInfoNew = (_ , New) , MergeInfoNew , MergeInfoNew
  -- merge-assoc (MergeInfoArrow x m1 m2 x₁) MergeInfoOld = {!   !}
  -- merge-assoc (MergeInfoArrow x m1 m2 x₁) (MergeInfoArrow x₂ m3 m4 x₃) = {!   !}



  syn-unicity : 
    ∀ {Γ e t1 t2} ->
    Γ ⊢ e ⇒ t1 ->
    Γ ⊢ e ⇒ t2 ->
    t1 ≡ t2
  syn-unicity (SynUp SynConst m1) (SynUp SynConst m2) = merge-syn-unicity m1 m2
  syn-unicity (SynUp SynHole m1) (SynUp SynHole m2) = merge-syn-unicity m1 m2
  syn-unicity (SynUp (SynFun syn1 refl) m1) (SynUp (SynFun syn2 refl) m2) with syn-unicity syn1 syn2 
  ... | refl = merge-syn-unicity m1 m2
  syn-unicity (SynUp (SynAp syn1 mt1 mn1 ana1) m1) (SynUp (SynAp syn2 mt2 mn2 ana2) m2) with syn-unicity syn1 syn2 
  ... | refl with ▸TArrow-unicity mt1 mt2 | ▸NArrow-unicity mn1 mn2 
  ... | refl , refl | refl , refl = merge-syn-unicity m1 m2
  syn-unicity (SynUp (SynApFail syn1 mt1 mn1 ana1) m1) (SynUp (SynApFail syn2 mt2 mn2 ana2) m2) with syn-unicity syn1 syn2 
  ... | refl with ▸NArrow-unicity mn1 mn2 
  ... | refl , refl = merge-syn-unicity m1 m2
  syn-unicity (SynUp (SynVar inctx1) m1) (SynUp (SynVar inctx2) m2) rewrite (ctx-unicity inctx1 inctx2) = merge-syn-unicity m1 m2
  syn-unicity (SynUp (SynVarFail _) m1) (SynUp (SynVarFail _) m2) = merge-syn-unicity m1 m2
  syn-unicity (SynUp (SynAsc _) m1) (SynUp (SynAsc _) m2) = merge-syn-unicity m1 m2
