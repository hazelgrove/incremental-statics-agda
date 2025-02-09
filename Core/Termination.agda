open import Data.Nat 
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.List
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

module Core.Termination where

  data iter {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} : ℕ -> (A -> A -> (Set ℓ₂)) -> (A -> A -> (Set (lmax ℓ₁ (lsuc ℓ₂)))) where 
    Iter0 : ∀ {R a} ->
      iter 0 R a a 
    IterS : ∀ {n R a b c} ->
      iter n R a b ->
      R b c -> 
      iter (suc n) R a c

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

  -- how many surface news, and set of all upstream positions of non-surface news

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
  <Score = _≡_

  <Score-wf : WellFounded <Score
  <Score-wf = {!   !}

  <Program : Program -> Program -> Set
  <Program p1 p2 = <Score (score-program p1) (score-program p2) 

  acc-translate : ∀ {p} ->
    Acc <Score (score-program p) ->
    Acc <Program p
  acc-translate (acc rs) = acc λ {p'} -> λ lt → acc-translate (rs lt)

  <Program-wf' : 
    (p : Program) -> 
    ∀ {p'} → 
    <Program p' p → 
    (Acc <Program p') 
  <Program-wf' p lt = acc-translate (<Score-wf _)

  <Program-wf : WellFounded <Program
  <Program-wf p = acc (<Program-wf' p)

  _↤P_ : Program -> Program -> Set 
  p' ↤P p = p P↦ p'

  StepDecrease : ∀ {p p'} ->
    p' ↤P p -> 
    <Program p' p
  StepDecrease = {!   !}

  acc-translate' : ∀ {p} ->
    Acc <Program p ->
    Acc _↤P_ p
  acc-translate' (acc rs) = acc λ {p'} -> λ lt → acc-translate' (rs (StepDecrease lt))

  ↤P-wf' :
    (p : Program) -> 
    ∀ {p'} → 
    p' ↤P p → 
    (Acc _↤P_ p') 
  ↤P-wf' p step = acc-translate' (<Program-wf _)

  ↤P-wf : WellFounded _↤P_
  ↤P-wf p = acc (↤P-wf' p)

  step-terminate : 
    (A : Set) -> 
    (R : A -> A -> Set) -> 
    (R-wf : WellFounded R) ->
    (p p' : A) ->
    ∃[ n ] ∃[ p' ] (iter n R p' p) × ¬ (∃[ p'' ] (R p' p''))
  step-terminate A R R-wf p p' with R-wf p'
  ... | acc rs = {! rs  !}

  TerminationProgram : ∀ {p} ->
    -- WellTypedProgram p ->
    ∃[ n ] ∃[ p' ] (iter n (_P↦_) p p') × (SettledProgram p')
  TerminationProgram = {!   !}
 
  