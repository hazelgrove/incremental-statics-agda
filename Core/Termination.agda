open import Data.Nat 
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
open import Data.Sum renaming (inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Induction.WellFounded 
open import Relation.Binary.PropositionalEquality hiding (inspect; [_])
open import Prelude
open import Agda.Primitive using (Level; lzero; lsuc) renaming (_⊔_ to lmax)


open import Core.Core hiding (_⊓_)
open import Core.WellTyped
open import Core.Environment
open import Core.Lemmas-Preservation
open import Core.VarsSynthesize
open import Core.Update
open import Core.Settled
open import Core.SettledDec
open import Core.Progress
open import Core.UpdatePreservation

module Core.Termination where

  -- mutual 

  --   <-wf' : (x : ℕ) -> {y : ℕ} → (y < x) -> (Acc _<_ y)
  --   <-wf' zero () 
  --   <-wf' (suc x) (s≤s z≤n) = acc (λ ())
  --   <-wf' (2+ zero) (s≤s (s≤s z≤n)) = acc λ x → {! x  !}
  --   <-wf' (2+ (suc x)) (s≤s (s≤s z≤n)) = {!   !}
  --   <-wf' (2+ (suc x)) (s≤s (s≤s (s≤s lt))) = {!   !}

  --   <-wf : WellFounded _<_ 
  --   <-wf n = acc (<-wf' n)

  Score : Set 
  Score = ℕ × List ℕ

  mutual 
    stream-length-up : ExpUp -> ℕ
    stream-length-up (EConst ⇒ _) = 1
    stream-length-up (EHole ⇒ _) = 1
    stream-length-up (EVar _ _ ⇒ _) = 1
    stream-length-up (EFun _ _ _ _ e-body ⇒ _) = 1 + (stream-length-low e-body)
    stream-length-up (EAsc _ e-body ⇒ _) = 1 + (stream-length-low e-body)
    stream-length-up (EAp e-fun _ e-arg ⇒ _) = 1 + (stream-length-low e-fun) + (stream-length-low e-arg)

    stream-length-low : ExpLow -> ℕ
    stream-length-low (e [ _ ]⇐ _) = 1 + (stream-length-up e)

  new-number : Newness -> ℕ 
  new-number Old = 0
  new-number New = 1

  new-set : Newness -> ℕ -> List ℕ
  new-set Old _ = []
  new-set New x = [ x ]

  _set+_ : (List ℕ) -> (List ℕ) -> (List ℕ)
  _set+_ = {!   !}
  
  mutual 

    score-up : ExpUp -> (x : ℕ) -> (ℕ × List ℕ)
    score-up (EConst ⇒ (_ , n)) x = (0 , new-set n x)
    score-up (EHole ⇒ (_ , n)) x = (0 , new-set n x)
    score-up (EVar _ _ ⇒ (_ , n)) x = (0 , new-set n x)
    score-up (EAsc (_ , n-asc) e-body ⇒ (_ , n)) x with score-low e-body (suc x)
    ... | num , set = (new-number n-asc + num) , (new-set n x) set+ set
    score-up (EFun _ (_ , n-ann) _ _ e-body ⇒ (_ , n)) x with score-low e-body (suc x)
    ... | num , set = (new-number n-ann + num) , (new-set n x) set+ set
    score-up (EAp e-fun _ e-arg ⇒ (_ , n)) x with score-low e-arg (suc x) | score-low e-fun (suc x + stream-length-low e-arg) 
    ... | num-arg , set-arg | num-fun , set-fun = (num-fun + num-arg) , (((new-set n x) set+ set-arg) set+ set-fun)

    score-low : ExpLow -> ℕ -> (ℕ × List ℕ)
    score-low (e [ _ ]⇐ (_ , n)) x with score-up e (suc x)
    ... | num , set = num , ((new-set n x) set+ set)

  -- property: all the elements of the list returned are less than stream-length of the exp
  -- score-bounded : ∀ {e x} -> (proj₂ (score-low e x))
  -- score-bounded = ?

  score-program : Program -> Score
  score-program p = score-low (ExpLowOfProgram p) 0

  <Score : Score -> Score -> Set
  <Score = {!   !}

  <Score-wf : WellFounded <Score
  <Score-wf = {!   !}

  _↤P_ : Program -> Program -> Set 
  p' ↤P p = p P↦ p'

  StepDecrease : ∀ {p p'} ->
    p' ↤P p -> 
    <Score (score-program p') (score-program p)
  StepDecrease = {!   !}

  acc-translate : ∀ {p} ->
    Acc <Score (score-program p) ->
    Acc _↤P_ p
  acc-translate (acc rs) = acc λ {p'} -> λ lt → acc-translate (rs (StepDecrease lt))

  ↤P-wf' :
    (p : Program) -> 
    ∀ {p'} → 
    p' ↤P p → 
    (Acc _↤P_ p') 
  ↤P-wf' p step = acc-translate (<Score-wf _)

  ↤P-wf : WellFounded _↤P_
  ↤P-wf p = acc (↤P-wf' p)

  data iter {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} : ℕ -> (A -> A -> (Set ℓ₂)) -> (A -> A -> (Set (lmax ℓ₁ (lsuc ℓ₂)))) where 
    Iter0 : ∀ {R a} ->
      iter 0 R a a 
    IterS : ∀ {n R a b c} ->
      R a b -> 
      iter n R b c ->
      iter (suc n) R a c

  TerminationProgramRec : 
    {p : Program} ->
    (Acc _↤P_ p) ->
    (WellTypedProgram p) ->
    ∃[ n ] ∃[ p' ] (iter n (_P↦_) p p') × (SettledProgram p')
  TerminationProgramRec {p} (acc recursor) wt with settled-dec p | ProgressProgram wt 
  ... | Inl settled | _ = 0 , p , Iter0 , settled
  ... | Inr unsettled | Inr settled = ⊥-elim (unsettled settled)
  ... | Inr unsettled | Inl (p' , step) with TerminationProgramRec {p'} (recursor step) (PreservationProgram wt step)
  ... | n , p'' , steps , settled = suc n , p'' , IterS step steps , settled

  TerminationProgram : 
    {p : Program} ->
    (WellTypedProgram p) ->
    ∃[ n ] ∃[ p' ] (iter n (_P↦_) p p') × (SettledProgram p')
  TerminationProgram wt = TerminationProgramRec (↤P-wf _) wt
  