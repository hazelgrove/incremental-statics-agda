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

  --   <-wf' : (x : ℕ) -> {y : ℕ} -> (y < x) -> (Acc _<_ y)
  --   <-wf' zero () 
  --   <-wf' (suc x) (s≤s z≤n) = acc (λ ())
  --   <-wf' (2+ zero) (s≤s (s≤s z≤n)) = acc λ x -> {! x  !}
  --   <-wf' (2+ (suc x)) (s≤s (s≤s z≤n)) = {!   !}
  --   <-wf' (2+ (suc x)) (s≤s (s≤s (s≤s lt))) = {!   !}

  --   <-wf : WellFounded _<_ 
  --   <-wf n = acc (<-wf' n)


  -- mutual 
  --   stream-length-up : ExpUp -> ℕ
  --   stream-length-up (EConst ⇒ _) = 1
  --   stream-length-up (EHole ⇒ _) = 1
  --   stream-length-up (EVar _ _ ⇒ _) = 1
  --   stream-length-up (EFun _ _ _ _ e-body ⇒ _) = 1 + (stream-length-low e-body)
  --   stream-length-up (EAsc _ e-body ⇒ _) = 1 + (stream-length-low e-body)
  --   stream-length-up (EAp e-fun _ e-arg ⇒ _) = 1 + (stream-length-low e-fun) + (stream-length-low e-arg)

  --   stream-length-low : ExpLow -> ℕ
  --   stream-length-low (e [ _ ]⇐ _) = 1 + (stream-length-up e)

  -- new-number : Newness -> ℕ 
  -- new-number Old = 0
  -- new-number New = 1

  -- new-set : Newness -> ℕ -> List ℕ
  -- new-set Old _ = []
  -- new-set New x = [ x ]

  -- _set+_ : (List ℕ) -> (List ℕ) -> (List ℕ)
  -- _set+_ = {!   !}

  -- Score : Set 
  -- Score = ℕ × List ℕ
  
  -- mutual 

  --   -- the second component is a decreasing list of non-repeating naturals, all of which 
  --   -- at greater than or equal to x and less than or equal to x + stream-length e
  --   score-up : ExpUp -> (x : ℕ) -> (ℕ × List ℕ)
  --   score-up (EConst ⇒ (_ , n)) x = (0 , new-set n x)
  --   score-up (EHole ⇒ (_ , n)) x = (0 , new-set n x)
  --   score-up (EVar _ _ ⇒ (_ , n)) x = (0 , new-set n x)
  --   score-up (EAsc (_ , n-asc) e-body ⇒ (_ , n)) x with score-low e-body (suc x)
  --   ... | num , set = (new-number n-asc + num) , set ++ (new-set n x)
  --   score-up (EFun _ (_ , n-ann) _ _ e-body ⇒ (_ , n)) x with score-low e-body (suc x)
  --   ... | num , set = (new-number n-ann + num) , set ++ (new-set n x)
  --   score-up (EAp e-fun _ e-arg ⇒ (_ , n)) x with score-low e-arg (suc x) | score-low e-fun (suc x + stream-length-low e-arg) 
  --   ... | num-arg , set-arg | num-fun , set-fun = (num-fun + num-arg) , (set-fun ++ set-arg ++ (new-set n x))

  --   score-low : ExpLow -> ℕ -> (ℕ × List ℕ)
  --   score-low (e [ _ ]⇐ (_ , n)) x with score-up e (suc x)
  --   ... | num , set = num , ((new-set n x) set+ set)

  -- -- property: all the elements of the list returned are less than stream-length of the exp
  -- -- score-bounded : ∀ {e x} -> (proj₂ (score-low e x))
  -- -- score-bounded = ?

  -- score-program : Program -> Score
  -- score-program p = score-low (ExpLowOfProgram p) 0

  -- data <Set : (List ℕ) -> (List ℕ) -> Set where 
  --   <SetEmpty : ∀ {h t} ->
  --     <Set [] (h ∷ t)
  --   <SetHead : ∀ {h1 h2 t1 t2} ->
  --     h1 < h2 -> 
  --     <Set (h1 ∷ t1) (h2 ∷ t2)
  --   <SetTail : ∀ {h t1 t2} ->
  --     <Set t1 t2 -> 
  --     <Set (h ∷ t1) (h ∷ t2)

  -- data <Score : Score -> Score -> Set where 
  --   <ScoreNum : ∀ {n1 n2 s1 s2} ->
  --     (n1 < n2) -> 
  --     <Score (n1 , s1) (n2 , s2)
  --   <ScoreSet : ∀ {n1 n2 s1 s2} ->
  --     (n1 ≡ n2) -> 
  --     (<Set s1 s2) -> 
  --     <Score (n1 , s1) (n2 , s2)

  -- <Score-wf : WellFounded <Score
  -- <Score-wf = {!   !}

  _↤P_ : Program -> Program -> Set 
  p' ↤P p = p P↦ p'

  -- direct approach 

  new-number : Newness -> ℕ 
  new-number Old = 0
  new-number New = 1

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

  data <New : NewData -> NewData -> Set where 
    <NewC : ∀ {t1 t2} ->
      <New (t1 , Old) (t2 , New)

  mutual 

    data <Up : ExpUp -> ExpUp -> Set where 
      <Upper : ∀ {e1 e2 syn1 syn2} ->
        <Mid e1 e2 ->  
        <Up (e1 ⇒ syn1) (e2 ⇒ syn2)
      <Upper= : ∀ {e syn1 syn2} ->
        -- =Mid e1 e2 ->
        <New syn1 syn2 ->  
        <Up (e ⇒ syn1) (e ⇒ syn2)
      
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
      <Ap=< : ∀ {a1 a2 e1 e2 e3} ->
        <Low e2 e3 -> 
        <Mid (EAp e1 a1 e2) (EAp e1 a2 e3)

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
  
  vars-syn-preserves-surface-news : ∀{x t m e e'} ->
    VarsSynthesize x t m e e' ->
    surface-news-up e ≡ surface-news-up e'
  vars-syn-preserves-surface-news VSConst = refl
  vars-syn-preserves-surface-news VSHole = refl
  vars-syn-preserves-surface-news VSVarEq = refl
  vars-syn-preserves-surface-news (VSVarNeq _) = refl
  vars-syn-preserves-surface-news VSFunEq = refl
  vars-syn-preserves-surface-news (VSFunNeq _ vars-syn) 
    rewrite vars-syn-preserves-surface-news vars-syn = refl
  vars-syn-preserves-surface-news (VSAsc vars-syn) 
    rewrite vars-syn-preserves-surface-news vars-syn = refl
  vars-syn-preserves-surface-news (VSAp vars-syn1 vars-syn2) 
    rewrite vars-syn-preserves-surface-news vars-syn1
    rewrite vars-syn-preserves-surface-news vars-syn2 = refl

  vars-syn?-preserves-surface-news : ∀{x t m e e'} ->
    VarsSynthesize? x t m e e' ->
    surface-news-up e ≡ surface-news-up e'
  vars-syn?-preserves-surface-news {BHole} refl = refl
  vars-syn?-preserves-surface-news {BVar x} = vars-syn-preserves-surface-news

  StepDecreaseU : ∀ {e e'} ->
    e U↦ e' -> 
    <ExpUp e' e
  StepDecreaseU StepAsc = <ExpUp< (n<1+n _)
  StepDecreaseU (StepAp x) = <ExpUp= refl (<Upper (<Ap< (<Lower= =New-refl (<Upper= <NewC))))

  StepDecreaseL : ∀ {e e'} ->
    e L↦ e' -> 
    <ExpLow e' e
  StepDecreaseL (StepNewAnnFun {e-body = e} {e-body' = e'} _ _ vars-syn) = <ExpLow< helper
    where 
    helper : surface-news-mid e' < suc (surface-news-mid e)
    helper rewrite (vars-syn?-preserves-surface-news vars-syn) = ≤-refl
  StepDecreaseL (StepNewSynConsist x) = <ExpLow= refl (<Lower= =NewOld (<Upper= <NewC))
  StepDecreaseL (StepNewAnaConsist x x₁) = <ExpLow= refl (<Lower <NewC)
  StepDecreaseL (StepAnaFun x x₁) = <ExpLow= refl (<Lower <NewC)
  StepDecreaseL StepSynFun = <ExpLow= refl (<Lower= =New-refl (<Upper (<Fun (<Lower= =NewOld (<Upper= <NewC)))))

  -- environment stuff

  mutual 
    
    surface-news-uu : UEnvUp -> ℕ
    surface-news-uu U⊙ = 0
    surface-news-uu (UEnvUpRec ε _) = surface-news-um ε

    surface-news-um : UEnvMid -> ℕ
    surface-news-um (UEnvAsc (_ , n-asc) ε) = (new-number n-asc) + surface-news-ul ε
    surface-news-um (UEnvFun _ (_ , n-ann) _ _ ε) = (new-number n-ann) + surface-news-ul ε
    surface-news-um (UEnvAp1 ε _ e-arg) = surface-news-ul ε + surface-news-low e-arg
    surface-news-um (UEnvAp2 e-fun _ ε) = surface-news-low e-fun + surface-news-ul ε

    surface-news-ul : UEnvLow -> ℕ
    surface-news-ul (UEnvLowRec ε _ _) = surface-news-uu ε

  mutual
    surface-news-lu : LEnvUp -> ℕ
    surface-news-lu (LEnvUpRec ε _) = surface-news-lm ε

    surface-news-lm : LEnvMid -> ℕ
    surface-news-lm (LEnvAsc (_ , n-asc) ε) = (new-number n-asc) + surface-news-ll ε
    surface-news-lm (LEnvFun _ (_ , n-ann) _ _ ε) = (new-number n-ann) + surface-news-ll ε
    surface-news-lm (LEnvAp1 ε _ e-arg) = surface-news-ll ε + surface-news-low e-arg
    surface-news-lm (LEnvAp2 e-fun _ ε) = surface-news-low e-fun + surface-news-ll ε

    surface-news-ll : LEnvLow -> ℕ
    surface-news-ll L⊙ = 0
    surface-news-ll (LEnvLowRec ε _ _) = surface-news-lu ε

  mutual 

    FillUEnvUp-surface : ∀ {ε e e-in} ->
      ε U⟦ e-in ⟧Up== e ->
      surface-news-up e ≡ surface-news-uu ε + surface-news-up e-in
    FillUEnvUp-surface FillU⊙ = refl
    FillUEnvUp-surface (FillUEnvUpRec fill) = FillUEnvMid-surface fill

    FillUEnvMid-surface : ∀ {ε e e-in} ->
      ε U⟦ e-in ⟧Mid== e ->
      surface-news-mid e ≡ surface-news-um ε + surface-news-up e-in 
    FillUEnvMid-surface {e-in = e-in} (FillUEnvAsc {ε = ε} {t = (_ , n)} fill) 
      rewrite FillUEnvLow-surface fill 
      =  sym (+-assoc (new-number n) (surface-news-ul ε) (surface-news-up e-in))
    FillUEnvMid-surface {e-in = e-in} (FillUEnvFun {ε = ε} {t = (_ , n)} fill) 
      rewrite FillUEnvLow-surface fill 
      = sym (+-assoc (new-number n) (surface-news-ul ε) (surface-news-up e-in))
    FillUEnvMid-surface {e-in = e-in} (FillUEnvAp1 {ε = ε} {e2 = e2} fill) 
      rewrite FillUEnvLow-surface fill 
      rewrite (+-assoc (surface-news-ul ε) (surface-news-up e-in) (surface-news-low e2))
      rewrite +-comm (surface-news-up e-in) (surface-news-low e2) 
      rewrite sym (+-assoc (surface-news-ul ε) (surface-news-low e2) (surface-news-up e-in))
      = refl
    FillUEnvMid-surface {e-in = e-in} (FillUEnvAp2 {ε = ε} {e1 = e1} fill) 
      rewrite FillUEnvLow-surface fill 
      = sym (+-assoc (surface-news-low e1) (surface-news-ul ε) (surface-news-up e-in))

    FillUEnvLow-surface : ∀ {ε e e-in} ->
      ε U⟦ e-in ⟧Low== e ->
      surface-news-low e ≡ surface-news-ul ε + surface-news-up e-in
    FillUEnvLow-surface (FillUEnvLowRec fill) = FillUEnvUp-surface fill

  mutual 

    FillLEnvUp-surface : ∀ {ε e e-in} ->
      ε L⟦ e-in ⟧Up== e ->
      surface-news-up e ≡ surface-news-lu ε + surface-news-low e-in
    FillLEnvUp-surface (FillLEnvUpRec fill) = FillLEnvMid-surface fill

    FillLEnvMid-surface : ∀ {ε e e-in} ->
      ε L⟦ e-in ⟧Mid== e ->
      surface-news-mid e ≡ surface-news-lm ε + surface-news-low e-in 
    FillLEnvMid-surface {e-in = e-in} (FillLEnvAsc {ε = ε} {t = (_ , n)} fill) 
      rewrite FillLEnvLow-surface fill 
      =  sym (+-assoc (new-number n) (surface-news-ll ε) (surface-news-low e-in))
    FillLEnvMid-surface {e-in = e-in} (FillLEnvFun {ε = ε} {t = (_ , n)} fill) 
      rewrite FillLEnvLow-surface fill 
      = sym (+-assoc (new-number n) (surface-news-ll ε) (surface-news-low e-in))
    FillLEnvMid-surface {e-in = e-in} (FillLEnvAp1 {ε = ε} {e2 = e2} fill) 
      rewrite FillLEnvLow-surface fill 
      rewrite (+-assoc (surface-news-ll ε) (surface-news-low e-in) (surface-news-low e2))
      rewrite +-comm (surface-news-low e-in) (surface-news-low e2) 
      rewrite sym (+-assoc (surface-news-ll ε) (surface-news-low e2) (surface-news-low e-in))
      = refl
    FillLEnvMid-surface {e-in = e-in} (FillLEnvAp2 {ε = ε} {e1 = e1} fill) 
      rewrite FillLEnvLow-surface fill 
      = sym (+-assoc (surface-news-low e1) (surface-news-ll ε) (surface-news-low e-in))

    FillLEnvLow-surface : ∀ {ε e e-in} ->
      ε L⟦ e-in ⟧Low== e ->
      surface-news-low e ≡ surface-news-ll ε + surface-news-low e-in
    FillLEnvLow-surface FillL⊙ = refl
    FillLEnvLow-surface (FillLEnvLowRec fill) = FillLEnvUp-surface fill 

  mutual 

    FillLEnvUp-<Up : ∀ {ε e e' e-in e-in'} ->
      ε L⟦ e-in' ⟧Up== e' ->
      ε L⟦ e-in ⟧Up== e ->
      <Low e-in' e-in ->
      <Up e' e
    FillLEnvUp-<Up (FillLEnvUpRec fill1) (FillLEnvUpRec fill2) lt = <Upper (FillLEnvMid-<Mid fill1 fill2 lt)

    FillLEnvMid-<Mid : ∀ {ε e e' e-in e-in'} ->
      ε L⟦ e-in' ⟧Mid== e' ->
      ε L⟦ e-in ⟧Mid== e ->
      <Low e-in' e-in ->
      <Mid e' e
    FillLEnvMid-<Mid (FillLEnvAsc fill1) (FillLEnvAsc fill2) lt = <Asc (FillLEnvLow-<Low fill1 fill2 lt) 
    FillLEnvMid-<Mid (FillLEnvFun fill1) (FillLEnvFun fill2) lt = <Fun (FillLEnvLow-<Low fill1 fill2 lt)
    FillLEnvMid-<Mid (FillLEnvAp1 fill1) (FillLEnvAp1 fill2) lt = <Ap< (FillLEnvLow-<Low fill1 fill2 lt) 
    FillLEnvMid-<Mid (FillLEnvAp2 fill1) (FillLEnvAp2 fill2) lt = <Ap=< (FillLEnvLow-<Low fill1 fill2 lt)

    FillLEnvLow-<Low : ∀ {ε e e' e-in e-in'} ->
      ε L⟦ e-in' ⟧Low== e' ->
      ε L⟦ e-in ⟧Low== e ->
      <Low e-in' e-in ->
      <Low e' e
    FillLEnvLow-<Low FillL⊙ FillL⊙ lt = lt
    FillLEnvLow-<Low (FillLEnvLowRec fill1) (FillLEnvLowRec fill2) lt = <Lower= =New-refl (FillLEnvUp-<Up fill1 fill2 lt)
  
  mutual 

    FillUEnvUp-<Up : ∀ {ε e e' e-in e-in'} ->
      ε U⟦ e-in' ⟧Up== e' ->
      ε U⟦ e-in ⟧Up== e ->
      <Up e-in' e-in ->
      <Up e' e
    FillUEnvUp-<Up FillU⊙ FillU⊙ lt = lt
    FillUEnvUp-<Up (FillUEnvUpRec fill1) (FillUEnvUpRec fill2) lt = <Upper (FillUEnvMid-<Mid fill1 fill2 lt)

    FillUEnvMid-<Mid : ∀ {ε e e' e-in e-in'} ->
      ε U⟦ e-in' ⟧Mid== e' ->
      ε U⟦ e-in ⟧Mid== e ->
      <Up e-in' e-in ->
      <Mid e' e
    FillUEnvMid-<Mid (FillUEnvAsc fill1) (FillUEnvAsc fill2) lt = <Asc (FillUEnvLow-<Low fill1 fill2 lt)
    FillUEnvMid-<Mid (FillUEnvFun fill1) (FillUEnvFun fill2) lt = <Fun (FillUEnvLow-<Low fill1 fill2 lt)
    FillUEnvMid-<Mid (FillUEnvAp1 fill1) (FillUEnvAp1 fill2) lt = <Ap< (FillUEnvLow-<Low fill1 fill2 lt)
    FillUEnvMid-<Mid (FillUEnvAp2 fill1) (FillUEnvAp2 fill2) lt = <Ap=< (FillUEnvLow-<Low fill1 fill2 lt)

    FillUEnvLow-<Low : ∀ {ε e e' e-in e-in'} ->
      ε U⟦ e-in' ⟧Low== e' ->
      ε U⟦ e-in ⟧Low== e ->
      <Up e-in' e-in ->
      <Low e' e
    FillUEnvLow-<Low (FillUEnvLowRec fill1) (FillUEnvLowRec fill2) lt = <Lower= =New-refl (FillUEnvUp-<Up fill1 fill2 lt)
    
  FillLEnvLow-<ExpLow : ∀ {ε e e' e-in e-in'} ->
    ε L⟦ e-in' ⟧Low== e' ->
    ε L⟦ e-in ⟧Low== e ->
    <ExpLow e-in' e-in ->
    <ExpLow e' e
  FillLEnvLow-<ExpLow {ε} {e} {e'} fill1 fill2 (<ExpLow< lt) = <ExpLow< lt'
    where 
    lt' : surface-news-low e' < surface-news-low e
    lt' 
      rewrite FillLEnvLow-surface fill1 
      rewrite FillLEnvLow-surface fill2 
      = +-monoʳ-< (surface-news-ll ε) lt
  FillLEnvLow-<ExpLow {ε} {e} {e'} fill1 fill2 (<ExpLow= eq lt) = <ExpLow= eq' (FillLEnvLow-<Low fill1 fill2 lt)
    where 
    eq' : surface-news-low e' ≡ surface-news-low e
    eq' 
      rewrite FillLEnvLow-surface fill1 
      rewrite FillLEnvLow-surface fill2 
      rewrite eq
      = refl

  FillUEnvLow-<ExpLow : ∀ {ε e e' e-in e-in'} ->
    ε U⟦ e-in' ⟧Low== e' ->
    ε U⟦ e-in ⟧Low== e ->
    <ExpUp e-in' e-in ->
    <ExpLow e' e
  FillUEnvLow-<ExpLow {ε} {e} {e'} fill1 fill2 (<ExpUp< lt) = <ExpLow< lt'
    where 
    lt' : surface-news-low e' < surface-news-low e
    lt' 
      rewrite FillUEnvLow-surface fill1 
      rewrite FillUEnvLow-surface fill2 
      = +-monoʳ-< (surface-news-ul ε) lt
  FillUEnvLow-<ExpLow {ε} {e} {e'} fill1 fill2 (<ExpUp= eq lt) = <ExpLow= eq' (FillUEnvLow-<Low fill1 fill2 lt)
    where 
    eq' : surface-news-low e' ≡ surface-news-low e
    eq' 
      rewrite FillUEnvLow-surface fill1 
      rewrite FillUEnvLow-surface fill2 
      rewrite eq
      = refl
  
  StepDecreaseLow : ∀ {e e'} ->
    e Low↦ e' -> 
    <ExpLow e' e
  StepDecreaseLow (StepLow fill1 step fill2) = FillLEnvLow-<ExpLow fill2 fill1 (StepDecreaseL step)
  StepDecreaseLow (StepUp fill1 step fill2) = FillUEnvLow-<ExpLow fill2 fill1 (StepDecreaseU step)

  StepDecrease : ∀ {p p'} ->
    p' ↤P p -> 
    <Program p' p 
  StepDecrease TopStep = <Program= refl (<Lower= =New-refl (<Upper= <NewC))
  StepDecrease (InsideStep step) with StepDecreaseLow step
  ... | <ExpLow< lt = <Program< lt
  ... | <ExpLow= eq lt = <Program= eq lt

  -- well-foundedness 
  
  mutual 
    translate-acc-up-old' : ∀{e t} ->
      Acc <Mid e ->
      ∀ {e'} ->
      (<Up e' (e ⇒ (t , Old))) -> 
      (Acc <Up e')
    translate-acc-up-old' ac (<Upper x) = translate-acc-up (<Mid-wf' _ x)
    
    translate-acc-up-old : ∀{e t} ->
      Acc <Mid e ->
      Acc <Up (e ⇒ (t , Old))
    translate-acc-up-old ac = acc (translate-acc-up-old' ac)

    translate-acc-up' : ∀{e syn} ->
      Acc <Mid e ->
      ∀ {e'} ->
      (<Up e' (e ⇒ syn)) -> 
      (Acc <Up e') 
    translate-acc-up' (acc ac) (<Upper x) = translate-acc-up (ac x)
    translate-acc-up' ac (<Upper= <NewC) = {!   !}

    translate-acc-up : ∀{e syn} ->
      Acc <Mid e ->
      Acc <Up (e ⇒ syn)
    translate-acc-up ac = acc (translate-acc-up' ac)
    
    <Up-wf-old' : 
      (e : ExpMid) -> 
      {t : Data} -> 
      ∀ {e'} ->
      (<Up e' (e ⇒ (t , Old))) -> 
      (Acc <Up e') 
    <Up-wf-old' e (<Upper lt) =  translate-acc-up (<Mid-wf' _ lt)

    <Up-wf-old : 
      (e : ExpMid) -> 
      {t : Data} -> 
      (Acc <Up (e ⇒ (t , Old))) 
    <Up-wf-old e = acc (<Up-wf-old' e)

    <Up-wf' : 
      (e : ExpUp) -> 
      ∀ {e'} ->
      (<Up e' e) -> 
      (Acc <Up e') 
    <Up-wf' e (<Upper lt) = translate-acc-up (<Mid-wf' _ lt)
    <Up-wf' (e ⇒ (_ , .New)) (<Upper= <NewC) = <Up-wf-old e

    <Mid-wf' : 
      (e : ExpMid) -> 
      ∀ {e'} ->
      (<Mid e' e) -> 
      (Acc <Mid e') 
    <Mid-wf' EConst ()
    <Mid-wf' EHole ()
    <Mid-wf' (EVar _ _) ()
    <Mid-wf' (EAsc _ e) (<Asc lt) with <Low-wf' e lt
    ... | thing = {!   !}
    <Mid-wf' (EFun _ _ _ _ e) (<Fun lt) = {!   !}
    <Mid-wf' (EAp e _ _) (<Ap< lt) = {!   !}
    <Mid-wf' (EAp _ _ e) (<Ap=< lt) = {!   !}

    <Mid-wf : WellFounded <Mid 
    <Mid-wf = {!   !}

    <Low-wf' : 
      (e : ExpLow) -> 
      ∀ {e'} ->
      (<Low e' e) -> 
      (Acc <Low e') 
    <Low-wf' (e [ _ ]⇐ _) (<Lower <NewC) = {!   !}
    <Low-wf' (e [ _ ]⇐ _) (<Lower= =NewOld lt) with <Up-wf' e lt
    ... | thing = {!   !}
    <Low-wf' (e [ _ ]⇐ _) (<Lower= =NewNew lt) with <Up-wf' e lt
    ... | thing = {!   !}

  <Low-wf : WellFounded <Low 
  <Low-wf e = acc (<Low-wf' e)

  -- mutual 

    -- <Program-wf-2 : 
    --   (p : Program) -> 
    --   (n : ℕ) -> 
    --   (surface-news-low (ExpLowOfProgram p) ≡ n) ->
    --   ∀ {p'} ->
    --   (surface-news-low (ExpLowOfProgram p') <
    --   surface-news-low (ExpLowOfProgram p)) -> 
    --   (Acc <Program p')
    -- <Program-wf-2 p zero eq lt rewrite eq with lt 
    -- ... | () 
    -- <Program-wf-2 p (suc n) eq {p'} lt =  <Program-wf-22 p' (surface-news-low (ExpLowOfProgram p')) refl

    -- <Program-wf-22 : 
    --   (p : Program) -> 
    --   (n : ℕ) -> 
    --   (surface-news-low (ExpLowOfProgram p) ≡ n) ->
    --   (Acc <Program p)
    -- <Program-wf-22 p n eq = acc helper
    --   where 
    --   helper : {y : Program} → <Program y p → Acc <Program y
    --   helper (<Program< lt) = <Program-wf-2 p _ refl lt
    --   helper (<Program= eq lt) = {!   !}

  <Program-wf' : 
    (p : Program) -> 
    ∀ {p'} ->
    (<Program p' p) -> 
    (Acc <Program p') 
  <Program-wf' p (<Program< lt) = {!   !} --<Program-wf-2 p _ refl lt
  <Program-wf' p (<Program= eq lt) = {!   !}

  <Program-wf : WellFounded <Program 
  <Program-wf p = acc (<Program-wf' p)

  acc-translate : ∀ {p} ->
    Acc <Program p ->
    Acc _↤P_ p
  acc-translate (acc rs) = acc λ {p'} -> λ lt -> acc-translate (rs (StepDecrease lt))

  ↤P-wf' :
    (p : Program) -> 
    ∀ {p'} -> 
    p' ↤P p -> 
    (Acc _↤P_ p') 
  ↤P-wf' p step = acc-translate (<Program-wf _)

  ↤P-wf : WellFounded _↤P_
  ↤P-wf p = acc (↤P-wf' p)

  data _P↦*_ : Program -> Program -> Set where 
    P↦0 : ∀ {p} ->
      p P↦* p
    P↦suc : ∀ {p p' p''} ->
      p P↦ p' -> 
      p' P↦* p'' ->
      p P↦* p''

  TerminationProgramRec : 
    {p : Program} ->
    (Acc _↤P_ p) ->
    (WellTypedProgram p) ->
    ∃[ p' ] (p P↦* p') × (SettledProgram p')
  TerminationProgramRec {p} (acc recursor) wt with settled-dec p | ProgressProgram wt 
  ... | Inl settled | _ = p , P↦0 , settled
  ... | Inr unsettled | Inr settled = ⊥-elim (unsettled settled)
  ... | Inr unsettled | Inl (p' , step) with TerminationProgramRec {p'} (recursor step) (PreservationProgram wt step)
  ... | p'' , steps , settled = p'' , P↦suc step steps , settled
 
  TerminationProgram : 
    {p : Program} ->
    (WellTypedProgram p) ->
    ∃[ p' ] (p P↦* p') × (SettledProgram p')
  TerminationProgram wt = TerminationProgramRec (↤P-wf _) wt
    