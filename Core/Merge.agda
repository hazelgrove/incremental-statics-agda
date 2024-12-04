open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.Merge where

data _▷_==n_ : NewType -> NewType -> Newness -> Set where 
  MergeInfoNew : ∀ {t1 t2 n2} -> 
    (t1 , New) ▷ (t2 , n2) ==n New
  MergeInfoOld : ∀ {t1 n2} -> 
    (t1 , Old) ▷ (t1 , n2) ==n n2
  MergeInfoArrow : ∀ {t1 t2 t3 t4 n n1 n2 n3 n4 n5 n6 n7} -> 
    n ▸NArrow n3 , n4 ->
    (t1 , n1) ▷ (t3 , n3) ==n n5 ->
    (t2 , n2) ▷ (t4 , n4) ==n n6 ->
    narrow n5 n6 ≡ n7 ->
    (TArrow t1 t2 , NArrow n1 n2) ▷ (TArrow t3 t4 , n) ==n n7

data _▷_==_ : NewType -> NewType -> NewType -> Set where
  MergeInfoType : ∀ {t1 n1 t2 n2} ->
    (t1 , n1) ▷ t2 ==n n2 ->
    (t1 , n1) ▷ t2 == (t1 , n2)

data MergeSyn : NewType -> SynData -> NewType -> Set where 
  MergeSynVoid : ∀ {t n} -> 
    MergeSyn (t , n) ̸⇑ (t , n)
  MergeSynMerge : ∀ {syn1 syn2 syn3} -> 
    syn1 ▷ syn2 == syn3 ->
    MergeSyn syn1 (⇑ syn2) syn3

data MergeAna : NewType -> AnaData -> NewType -> Set where 
  MergeAnaVoid : ∀ {t n} -> 
    MergeAna (t , n) ̸⇓ (t , New)
  MergeAnaMerge : ∀ {ana1 ana2 ana3} -> 
    ana1 ▷ ana2 == ana3 ->
    MergeAna ana1 (⇓ ana2) ana3
