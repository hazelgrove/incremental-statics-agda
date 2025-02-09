open import Data.Nat 
open import Data.Nat.Properties
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

  Score : Set 
  Score = ℕ × List ℕ
  
  mutual 

    -- the second component is a decreasing list of non-repeating naturals, all of which 
    -- at greater than or equal to x and less than or equal to x + stream-length e
    score-up : ExpUp -> (x : ℕ) -> (ℕ × List ℕ)
    score-up (EConst ⇒ (_ , n)) x = (0 , new-set n x)
    score-up (EHole ⇒ (_ , n)) x = (0 , new-set n x)
    score-up (EVar _ _ ⇒ (_ , n)) x = (0 , new-set n x)
    score-up (EAsc (_ , n-asc) e-body ⇒ (_ , n)) x with score-low e-body (suc x)
    ... | num , set = (new-number n-asc + num) , set ++ (new-set n x)
    score-up (EFun _ (_ , n-ann) _ _ e-body ⇒ (_ , n)) x with score-low e-body (suc x)
    ... | num , set = (new-number n-ann + num) , set ++ (new-set n x)
    score-up (EAp e-fun _ e-arg ⇒ (_ , n)) x with score-low e-arg (suc x) | score-low e-fun (suc x + stream-length-low e-arg) 
    ... | num-arg , set-arg | num-fun , set-fun = (num-fun + num-arg) , (set-fun ++ set-arg ++ (new-set n x))

    score-low : ExpLow -> ℕ -> (ℕ × List ℕ)
    score-low (e [ _ ]⇐ (_ , n)) x with score-up e (suc x)
    ... | num , set = num , ((new-set n x) set+ set)

  -- property: all the elements of the list returned are less than stream-length of the exp
  -- score-bounded : ∀ {e x} -> (proj₂ (score-low e x))
  -- score-bounded = ?

  score-program : Program -> Score
  score-program p = score-low (ExpLowOfProgram p) 0

  data <Set : (List ℕ) -> (List ℕ) -> Set where 
    <SetEmpty : ∀ {h t} ->
      <Set [] (h ∷ t)
    <SetHead : ∀ {h1 h2 t1 t2} ->
      h1 < h2 -> 
      <Set (h1 ∷ t1) (h2 ∷ t2)
    <SetTail : ∀ {h t1 t2} ->
      <Set t1 t2 -> 
      <Set (h ∷ t1) (h ∷ t2)

  data <Score : Score -> Score -> Set where 
    <ScoreNum : ∀ {n1 n2 s1 s2} ->
      (n1 < n2) -> 
      <Score (n1 , s1) (n2 , s2)
    <ScoreSet : ∀ {n1 n2 s1 s2} ->
      (n1 ≡ n2) -> 
      (<Set s1 s2) -> 
      <Score (n1 , s1) (n2 , s2)

  <Score-wf : WellFounded <Score
  <Score-wf = {!   !}

  _↤P_ : Program -> Program -> Set 
  p' ↤P p = p P↦ p'

  -- direct approach 

  mutual 
    surface-news-up : ExpUp -> ℕ
    surface-news-up (e ⇒ _) = surface-news-mid e

    surface-news-mid : ExpMid -> ℕ
    surface-news-mid (EConst) = 0
    surface-news-mid (EHole) = 0
    surface-news-mid (EVar _ _) = 0
    surface-news-mid (EAsc (_ , n-asc) e-body) = (new-number n-asc) + surface-news-low e-body
    surface-news-mid (EFun _ (_ , n-ann) _ _ e-body) = (new-number n-ann) + surface-news-low e-body
    surface-news-mid (EAp e-fun _ e-arg) = surface-news-low e-fun + surface-news-low e-arg

    surface-news-low : ExpLow -> ℕ
    surface-news-low (e [ _ ]⇐ _) = surface-news-up e

  data =New : NewData -> NewData -> Set where 
    =NewOld : ∀ {t1 t2} ->
      =New (t1 , Old) (t2 , Old)
    =NewNew : ∀ {t1 t2} ->
      =New (t1 , New) (t2 , New)

  =New-refl : ∀ {n} -> =New n n 
  =New-refl {_ , Old} = =NewOld
  =New-refl {_ , New} = =NewNew

  data =Up : ExpUp -> ExpUp -> Set where 

  data =Mid : ExpMid -> ExpMid -> Set where 

  data =Low : ExpLow -> ExpLow -> Set where 
    

  =Mid-refl : ∀ {e} -> =Mid e e 
  =Mid-refl = {!   !}

  data <New : NewData -> NewData -> Set where 
    <NewC : ∀ {t1 t2} ->
      <New (t1 , Old) (t2 , New)

  mutual 

    data <Up : ExpUp -> ExpUp -> Set where 
      <Upper : ∀ {e1 e2 syn1 syn2} ->
        <Mid e1 e2 ->  
        <Up (e1 ⇒ syn1) (e2 ⇒ syn2)
      <Upper= : ∀ {e1 e2 syn1 syn2} ->
        =Mid e1 e2 ->  
        <New syn1 syn2 ->  
        <Up (e1 ⇒ syn1) (e2 ⇒ syn2)
      
    data <Mid : ExpMid -> ExpMid -> Set where 
      <Asc : ∀ {a1 a2 e1 e2} ->
        <Low e1 e2 -> 
        <Mid (EAsc a1 e1) (EAsc a2 e2)
      <Fun : ∀ {a1 a2 a3 a4 a5 a6 a7 a8 e1 e2} ->
        <Low e1 e2 -> 
        <Mid (EFun a1 a2 a3 a4 e1) (EFun a5 a6 a7 a8 e2)
      <Ap< : ∀ {a1 a2 e1 e2 e3 e4} ->
        <Low e1 e3 -> 
        <Mid (EAp e1 a1 e2) (EAp e3 a2 e4)
      <Ap=< : ∀ {a1 a2 e1 e2 e3 e4} ->
        =Low e1 e3 -> 
        <Low e2 e4 -> 
        <Mid (EAp e1 a1 e2) (EAp e3 a2 e4)

    data <Low : ExpLow -> ExpLow -> Set where 
      <Lower : ∀ {e1 e2 a1 a2 ana1 ana2} ->
        <New ana1 ana2 ->  
        <Low (e1 [ a1 ]⇐ ana1) (e2 [ a2 ]⇐ ana2)
      <Lower= : ∀ {e1 e2 a1 a2 ana1 ana2} ->
        =New ana1 ana2 ->  
        <Up e1 e2 ->
        <Low (e1 [ a1 ]⇐ ana1) (e2 [ a2 ]⇐ ana2)

  data <Program : Program -> Program -> Set where 
    <Program< : ∀ {p p'} ->
      surface-news-low (ExpLowOfProgram p) < surface-news-low (ExpLowOfProgram p') -> 
      <Program p p'
    <Program= : ∀ {p p'} ->
      surface-news-low (ExpLowOfProgram p) ≡ surface-news-low (ExpLowOfProgram p') -> 
      <Low (ExpLowOfProgram p) (ExpLowOfProgram p') ->
      <Program p p'

  data <ExpUp : ExpUp -> ExpUp -> Set where 
    <ExpUp< : ∀ {e e'} ->
      surface-news-up e < surface-news-up e' -> 
      <ExpUp e e'
    <ExpUp= : ∀ {e e'} ->
      surface-news-up e ≡ surface-news-up e' -> 
      <Up e e' ->
      <ExpUp e e'

  data <ExpLow : ExpLow -> ExpLow -> Set where 
    <ExpLow< : ∀ {e e'} ->
      surface-news-low e < surface-news-low e' -> 
      <ExpLow e e'
    <ExpLow= : ∀ {e e'} ->
      surface-news-low e ≡ surface-news-low e' -> 
      <Low e e' ->
      <ExpLow e e'

  StepDecreaseU : ∀ {e e'} ->
    e U↦ e' -> 
    <ExpUp e' e
  StepDecreaseU = {!   !}

  StepDecreaseL : ∀ {e e'} ->
    e L↦ e' -> 
    <ExpLow e' e
  StepDecreaseL = {!   !}

  StepDecreaseUp : ∀ {e e'} ->
    e Up↦ e' -> 
    <ExpUp e' e
  StepDecreaseUp = {!   !}

  surface-news-ll : LEnvLow -> ℕ
  surface-news-ll = {!   !}

  FillLEnvLow-surface : ∀ {ε e e-in} ->
    ε L⟦ e-in ⟧Low== e ->
    surface-news-low e ≡ surface-news-low e-in + surface-news-ll ε
  FillLEnvLow-surface fill = {!   !}

  FillLEnvLow-mono' : ∀ {ε e e' e-in e-in'} ->
    ε L⟦ e-in' ⟧Low== e' ->
    ε L⟦ e-in ⟧Low== e ->
    <Low e-in' e-in ->
    <Low e' e
  FillLEnvLow-mono' = {!   !}

  FillLEnvLow-mono : ∀ {ε e e' e-in e-in'} ->
    ε L⟦ e-in' ⟧Low== e' ->
    ε L⟦ e-in ⟧Low== e ->
    <ExpLow e-in' e-in ->
    <ExpLow e' e
  FillLEnvLow-mono {ε} {e} {e'} fill1 fill2 (<ExpLow< lt) = <ExpLow< lt'
    where 
    lt' : surface-news-low e' < surface-news-low e
    lt' 
      rewrite FillLEnvLow-surface fill1 
      rewrite FillLEnvLow-surface fill2 
      = +-monoˡ-< (surface-news-ll ε) lt
  FillLEnvLow-mono {ε} {e} {e'} fill1 fill2 (<ExpLow= eq lt) = <ExpLow= eq' (FillLEnvLow-mono' fill1 fill2 lt)
    where 
    eq' : surface-news-low e' ≡ surface-news-low e
    eq' 
      rewrite FillLEnvLow-surface fill1 
      rewrite FillLEnvLow-surface fill2 
      rewrite eq
      = refl

  FillUEnvLow-mono : ∀ {ε e e' e-in e-in'} ->
    ε U⟦ e-in' ⟧Low== e' ->
    ε U⟦ e-in ⟧Low== e ->
    <ExpUp e-in' e-in ->
    <ExpLow e' e
  FillUEnvLow-mono = {!   !}

  StepDecreaseLow : ∀ {e e'} ->
    e Low↦ e' -> 
    <ExpLow e' e
  StepDecreaseLow (StepLow fill1 step fill2) = FillLEnvLow-mono fill2 fill1 (StepDecreaseL step)
  StepDecreaseLow (StepUp fill1 step fill2) with StepDecreaseU step 
  ... | thing = FillUEnvLow-mono fill2 fill1 thing
  
  -- StepDecreaseLow (StepLow FillL⊙ step FillL⊙) = StepDecreaseL step
  -- StepDecreaseLow (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)) with StepDecreaseUp (StepLow fill1 step fill2)
  -- ... | thing = {!   !}
  -- StepDecreaseLow (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)) with StepDecreaseU step
  -- ... | thing = {!   !}
  -- StepDecreaseLow (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))) with StepDecreaseLow {!   !}
  -- ... | thing = {!   !}

  StepDecrease' : ∀ {p p'} ->
    p' ↤P p -> 
    <Program p' p 
  StepDecrease' TopStep = <Program= refl (<Lower= =New-refl (<Upper= =Mid-refl <NewC))
  StepDecrease' (InsideStep step) with StepDecreaseLow step
  ... | <ExpLow< lt = <Program< lt
  ... | <ExpLow= eq lt = <Program= eq lt

  StepDecrease : ∀ {p p'} ->
    p' ↤P p -> 
    <Score (score-program p') (score-program p)
  StepDecrease (InsideStep x) = {!   !}
  StepDecrease TopStep = {!   !}

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
  