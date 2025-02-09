open import Data.Nat 
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)


open import Core.Core hiding (_⊓_)
open import Core.WellTyped
open import Core.Environment
open import Core.Lemmas-Preservation
open import Core.VarsSynthesize
open import Core.Update
open import Core.Settled

module Core.Termination where

  data iter {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} : ℕ -> (A -> A -> (Set ℓ₂)) -> (A -> A -> (Set (lmax ℓ₁ (lsuc ℓ₂)))) where 
    Iter0 : ∀ {R a} ->
      iter 0 R a a 
    IterS : ∀ {n R a b c} ->
      iter n R a b ->
      R b c -> 
      iter (suc n) R a c

  old-indicator : Newness -> ℕ 
  old-indicator Old = 1
  old-indicator New = 0

  postulate 
    x-binding : Binding

  puzzle-e1 : ExpLow 
  puzzle-e1 = ((EFun x-binding (THole , Old) ✔ ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (■ THole , Old))) ⇒ (□ , Old)) [ ✔ ]⇐ (■ THole , Old)
  puzzle-e2 : ExpLow 
  puzzle-e2 = ((EFun x-binding (THole , Old) ✔ ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (■ THole , Old))) ⇒ (□ , Old)) [ ✔ ]⇐ (□ , New)
  puzzle-e3 : ExpLow 
  puzzle-e3 = ((EFun x-binding (THole , Old) ✔ ✔ ((EHole ⇒ (■ THole , Old)) [ ✔ ]⇐ (□ , New))) ⇒ (□ , New)) [ ✔ ]⇐ (□ , Old)

  puzzle-e1-wt : ∅ ⊢ puzzle-e1 ⇐
  puzzle-e1-wt = AnaFun (NTArrowC (DTArrowSome MArrowHole))
    (■~N-pair (~N-pair (~DSome ConsistHoleL))) (▷Pair ▶Old) ▶Old ▶Old
    (▷Pair ▶Old) (~N-pair ~DVoidL) ▶Old
    (AnaSubsume SubsumableHole (~N-pair (~DSome ConsistHoleL)) ▶Old
     (SynHole (▷Pair ▶Old)))
  puzzle-e2-wt : ∅ ⊢ puzzle-e2 ⇐
  puzzle-e2-wt = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR))
    (▷Pair ▶New) ▶New ▶New (▷Pair ▶New) (~N-pair ~DVoidL) ▶New
    (AnaSubsume SubsumableHole (~N-pair (~DSome ConsistHoleL)) ▶Old
     (SynHole (▷Pair ▶Old)))
  puzzle-e3-wt : ∅ ⊢ puzzle-e3 ⇐
  puzzle-e3-wt =  AnaFun {!   !} {!   !} {!   !} {!   !} ▶Old {!   !} {!   !} {!   !} {!   !}

  -- thinking time: 
  -- each action either decreases the number of news in the surface syntax, or leaves it the same
  -- so use a lexicographic ordering with this as the first entry. this handles those steps that change
  -- surface news. 
  -- This leaves five: new syn, new ana, ana fun, syn fun, and ap
  -- new syn and new ana: just deletes a new. should be easy to handle. 
  -- ana fun : new pushed down through fun 
  -- syn fun : new pushed up through fun 
  -- ap : new pushed up and around, splitting. 

  -- issue: two directions for lambda, don't even align with modes (could be pushing around void)
  -- issue: ap splits

  -- not good enough:
  -- how long until encountering a new in the bidirectional flow
  mutual 

    score-syn : ExpUp -> ℕ
    score-syn (EConst ⇒ (t , n)) = old-indicator n
    score-syn (EHole ⇒ (t , n)) = old-indicator n
    score-syn (EAsc (t-asc , New) e-body ⇒ (t , n)) = 0
    score-syn (EAsc (t-asc , Old) e-body ⇒ (t , n)) = 1 + ((old-indicator n) ⊓ (score-ana e-body))
    score-syn (EFun x (t-ann , New) _ _ e-body ⇒ (t , n)) = 0
    score-syn (EFun x (t-ann , Old) _ _ e-body ⇒ (t , n)) = 1 + {!   !}
    score-syn (EAp e-fun m e-arg ⇒ (t , n)) = (old-indicator n) ⊓ (score-ana e-fun) ⊓ (score-ana e-arg)
    score-syn (EVar _ _ ⇒ (t , n)) = {!   !}

    score-ana : ExpLow -> ℕ
    score-ana = {!   !}


  TerminationProgram : ∀ {p} ->
    WellTypedProgram p ->
    ∃[ n ] ∃[ p' ] (iter n (_P↦_) p p') × (SettledProgram p')
  TerminationProgram (WTProg x) = {!   !}
