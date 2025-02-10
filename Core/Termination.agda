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
open import Core.Marking
open import Core.Update
open import Core.Settled
open import Core.SettledDec
open import Core.Progress
open import Core.UpdatePreservation

module Core.Termination where

  _↤P_ : Program -> Program -> Set 
  p' ↤P p = p P↦ p'

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

  data Skeleton : Set where 
    S0 : Skeleton 
    S1 : Skeleton -> Skeleton 
    S2 : Skeleton -> Skeleton -> Skeleton 

  mutual 

    SkelUp : ExpUp -> Skeleton 
    SkelUp (e ⇒ _) = SkelMid e

    SkelMid : ExpMid -> Skeleton 
    SkelMid EConst = S0
    SkelMid EHole = S0
    SkelMid (EVar _ _) = S0
    SkelMid (EAsc _ e) = S1 (SkelLow e)
    SkelMid (EFun _ _ _ _ e) = S1 (SkelLow e)
    SkelMid (EAp e1 _ e2) = S2 (SkelLow e1) (SkelLow e2)

    SkelLow : ExpLow -> Skeleton  
    SkelLow (e [ _ ]⇐ _) = SkelUp e

  SkelProgram : Program -> Skeleton 
  SkelProgram p = SkelLow (ExpLowOfProgram p)

  mutual 

    data <Up : Skeleton -> ExpUp -> ExpUp -> Set where 
      <Upper : ∀ {s e1 e2 syn1 syn2} ->
        <Mid s e1 e2 ->  
        <Up s (e1 ⇒ syn1) (e2 ⇒ syn2)
      <Upper= : ∀ {e syn1 syn2} ->
        <New syn1 syn2 ->  
        <Up (SkelMid e) (e ⇒ syn1) (e ⇒ syn2)
      
    data <Mid : Skeleton -> ExpMid -> ExpMid -> Set where 
      <Asc : ∀ {s a1 a2 e1 e2} ->
        <Low s e1 e2 -> 
        <Mid (S1 s) (EAsc a1 e1) (EAsc a2 e2)
      <Fun : ∀ {s a1 a2 a3 a4 a5 a6 a7 a8 e1 e2} ->
        <Low s e1 e2 -> 
        <Mid (S1 s) (EFun a1 a2 a3 a4 e1) (EFun a5 a6 a7 a8 e2)
      <Ap< : ∀ {s1 a1 a2 e1 e2 e3 e4} ->
        <Low s1 e1 e3 -> 
        <Mid (S2 s1 (SkelLow e2)) (EAp e1 a1 e2) (EAp e3 a2 e4)
      <Ap=< : ∀ {s2 a1 a2 e1 e2 e3} ->
        <Low s2 e2 e3 -> 
        <Mid (S2 (SkelLow e1) s2) (EAp e1 a1 e2) (EAp e1 a2 e3)

    data <Low : Skeleton -> ExpLow -> ExpLow -> Set where 
      <Lower : ∀ {e1 e2 a1 a2 ana1 ana2} ->
        <New ana1 ana2 ->  
        <Low (SkelUp e1) (e1 [ a1 ]⇐ ana1) (e2 [ a2 ]⇐ ana2)
      <Lower= : ∀ {s e1 e2 a1 a2 ana1 ana2} ->
        =New ana1 ana2 ->  
        <Up s e1 e2 ->
        <Low s (e1 [ a1 ]⇐ ana1) (e2 [ a2 ]⇐ ana2)

  data <Program : Program -> Program -> Set where 
    <Program< : ∀ {p p'} ->
      surface-news-low (ExpLowOfProgram p) < surface-news-low (ExpLowOfProgram p') -> 
      <Program p p'
    <Program= : ∀ {p p'} ->
      surface-news-low (ExpLowOfProgram p) ≡ surface-news-low (ExpLowOfProgram p') -> 
      <Low (SkelProgram p) (ExpLowOfProgram p) (ExpLowOfProgram p') ->
      <Program p p'

  data <ExpUp : ExpUp -> ExpUp -> Set where 
    <ExpUp< : ∀ {e e'} ->
      surface-news-up e < surface-news-up e' -> 
      <ExpUp e e'
    <ExpUp= : ∀ {e e'} ->
      surface-news-up e ≡ surface-news-up e' -> 
      <Up (SkelUp e) e e' ->
      <ExpUp e e'

  data <ExpLow : ExpLow -> ExpLow -> Set where 
    <ExpLow< : ∀ {e e'} ->
      surface-news-low e < surface-news-low e' -> 
      <ExpLow e e'
    <ExpLow= : ∀ {e e'} ->
      surface-news-low e ≡ surface-news-low e' -> 
      <Low (SkelLow e) e e' ->
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

  -- -- environment stuff

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


  data SkelEnv : Set where 
    S⊙ : SkelEnv
    SE1 : SkelEnv -> SkelEnv
    SEL : SkelEnv -> Skeleton -> SkelEnv
    SER : Skeleton -> SkelEnv -> SkelEnv

  SkelFill : Skeleton -> SkelEnv -> Skeleton 
  SkelFill s S⊙ = s
  SkelFill s (SE1 e) = S1 (SkelFill s e)
  SkelFill s (SEL e s2) = S2 (SkelFill s e) s2
  SkelFill s (SER s1 e) = S2 s1 (SkelFill s e)

  mutual 
    skel-lu : LEnvUp -> SkelEnv 
    skel-lu (LEnvUpRec e _) = skel-lm e

    skel-lm : LEnvMid -> SkelEnv 
    skel-lm (LEnvAsc _ e) = SE1 (skel-ll e)
    skel-lm (LEnvFun _ _ _ _ e) = SE1 (skel-ll e)
    skel-lm (LEnvAp1 e1 _ e2) = SEL (skel-ll e1) (SkelLow e2)
    skel-lm (LEnvAp2 e1 _ e2) = SER (SkelLow e1) (skel-ll e2)

    skel-ll : LEnvLow -> SkelEnv 
    skel-ll L⊙ = S⊙
    skel-ll (LEnvLowRec e _ _) = skel-lu e

  mutual 
    skel-uu : UEnvUp -> SkelEnv 
    skel-uu U⊙ = S⊙
    skel-uu (UEnvUpRec e _) = skel-um e

    skel-um : UEnvMid -> SkelEnv 
    skel-um (UEnvAsc _ e) = SE1 (skel-ul e)
    skel-um (UEnvFun _ _ _ _ e) = SE1 (skel-ul e)
    skel-um (UEnvAp1 e1 _ e2) = SEL (skel-ul e1) (SkelLow e2)
    skel-um (UEnvAp2 e1 _ e2) = SER (SkelLow e1) (skel-ul e2)

    skel-ul : UEnvLow -> SkelEnv 
    skel-ul (UEnvLowRec e _ _) = skel-uu e

  mutual 

    skel-lu-comm : ∀ {ε e e-in} ->
      ε L⟦ e-in ⟧Up== e ->
      SkelFill (SkelLow e-in) (skel-lu ε) ≡ SkelUp e
    skel-lu-comm (FillLEnvUpRec x) = skel-lm-comm x

    skel-lm-comm : ∀ {ε e e-in} ->
      ε L⟦ e-in ⟧Mid== e ->
      SkelFill (SkelLow e-in) (skel-lm ε) ≡ SkelMid e
    skel-lm-comm (FillLEnvFun x) = cong S1 (skel-ll-comm x)
    skel-lm-comm (FillLEnvAsc x) = cong S1 (skel-ll-comm x)
    skel-lm-comm (FillLEnvAp1 {e2 = e2} x) = cong (λ a -> S2 a (SkelLow e2)) (skel-ll-comm x)
    skel-lm-comm (FillLEnvAp2 {e1 = e1} x) = cong (S2 (SkelLow e1)) (skel-ll-comm x)

    skel-ll-comm : ∀ {ε e e-in} ->
      ε L⟦ e-in ⟧Low== e ->
      SkelFill (SkelLow e-in) (skel-ll ε) ≡ SkelLow e
    skel-ll-comm FillL⊙ = refl
    skel-ll-comm (FillLEnvLowRec x) = skel-lu-comm x

  mutual 

    skel-uu-comm : ∀ {ε e e-in} ->
      ε U⟦ e-in ⟧Up== e ->
      SkelFill (SkelUp e-in) (skel-uu ε) ≡ SkelUp e
    skel-uu-comm FillU⊙ = refl
    skel-uu-comm (FillUEnvUpRec x) = skel-um-comm x

    skel-um-comm : ∀ {ε e e-in} ->
      ε U⟦ e-in ⟧Mid== e ->
      SkelFill (SkelUp e-in) (skel-um ε) ≡ SkelMid e
    skel-um-comm (FillUEnvFun x) = cong S1 (skel-ul-comm x)
    skel-um-comm (FillUEnvAsc x) = cong S1 (skel-ul-comm x)
    skel-um-comm (FillUEnvAp1 {e2 = e2} x) = cong (λ a -> S2 a (SkelLow e2)) (skel-ul-comm x)
    skel-um-comm (FillUEnvAp2 {e1 = e1} x) = cong (S2 (SkelLow e1)) (skel-ul-comm x)

    skel-ul-comm : ∀ {ε e e-in} ->
      ε U⟦ e-in ⟧Low== e ->
      SkelFill (SkelUp e-in) (skel-ul ε) ≡ SkelLow e
    skel-ul-comm (FillUEnvLowRec x) = skel-uu-comm x


  mutual 

    FillLEnvUp-<Up : ∀ {ε e e' e-in e-in' s} ->
      ε L⟦ e-in' ⟧Up== e' ->
      ε L⟦ e-in ⟧Up== e ->
      <Low s e-in' e-in ->
      <Up (SkelFill s (skel-lu ε)) e' e
    FillLEnvUp-<Up (FillLEnvUpRec fill1) (FillLEnvUpRec fill2) lt = <Upper (FillLEnvMid-<Mid fill1 fill2 lt)

    FillLEnvMid-<Mid : ∀ {ε e e' e-in e-in' s} ->
      ε L⟦ e-in' ⟧Mid== e' ->
      ε L⟦ e-in ⟧Mid== e ->
      <Low s e-in' e-in ->
      <Mid (SkelFill s (skel-lm ε)) e' e
    FillLEnvMid-<Mid (FillLEnvAsc fill1) (FillLEnvAsc fill2) lt = <Asc (FillLEnvLow-<Low fill1 fill2 lt)
    FillLEnvMid-<Mid (FillLEnvFun fill1) (FillLEnvFun fill2) lt = <Fun (FillLEnvLow-<Low fill1 fill2 lt)
    FillLEnvMid-<Mid (FillLEnvAp1 fill1) (FillLEnvAp1 fill2) lt = <Ap< (FillLEnvLow-<Low fill1 fill2 lt)
    FillLEnvMid-<Mid (FillLEnvAp2 fill1) (FillLEnvAp2 fill2) lt = <Ap=< (FillLEnvLow-<Low fill1 fill2 lt)

    FillLEnvLow-<Low : ∀ {ε e e' e-in e-in' s} ->
      ε L⟦ e-in' ⟧Low== e' ->
      ε L⟦ e-in ⟧Low== e ->
      <Low s e-in' e-in ->
      <Low (SkelFill s (skel-ll ε)) e' e
    FillLEnvLow-<Low FillL⊙ FillL⊙ lt = lt
    FillLEnvLow-<Low (FillLEnvLowRec fill1) (FillLEnvLowRec fill2) lt = <Lower= =New-refl (FillLEnvUp-<Up fill1 fill2 lt)
  
  mutual 

    FillUEnvUp-<Up : ∀ {ε e e' e-in e-in' s} ->
      ε U⟦ e-in' ⟧Up== e' ->
      ε U⟦ e-in ⟧Up== e ->
      <Up s e-in' e-in ->
      <Up (SkelFill s (skel-uu ε)) e' e
    FillUEnvUp-<Up FillU⊙ FillU⊙ lt = lt
    FillUEnvUp-<Up (FillUEnvUpRec fill1) (FillUEnvUpRec fill2) lt = <Upper (FillUEnvMid-<Mid fill1 fill2 lt)

    FillUEnvMid-<Mid : ∀ {ε e e' e-in e-in' s} ->
      ε U⟦ e-in' ⟧Mid== e' ->
      ε U⟦ e-in ⟧Mid== e ->
      <Up s e-in' e-in ->
      <Mid (SkelFill s (skel-um ε)) e' e
    FillUEnvMid-<Mid (FillUEnvAsc fill1) (FillUEnvAsc fill2) lt = <Asc (FillUEnvLow-<Low fill1 fill2 lt)
    FillUEnvMid-<Mid (FillUEnvFun fill1) (FillUEnvFun fill2) lt = <Fun (FillUEnvLow-<Low fill1 fill2 lt)
    FillUEnvMid-<Mid (FillUEnvAp1 fill1) (FillUEnvAp1 fill2) lt = <Ap< (FillUEnvLow-<Low fill1 fill2 lt)
    FillUEnvMid-<Mid (FillUEnvAp2 fill1) (FillUEnvAp2 fill2) lt = <Ap=< (FillUEnvLow-<Low fill1 fill2 lt)

    FillUEnvLow-<Low : ∀ {ε e e' e-in e-in' s} ->
      ε U⟦ e-in' ⟧Low== e' ->
      ε U⟦ e-in ⟧Low== e ->
      <Up s e-in' e-in ->
      <Low (SkelFill s (skel-ul ε)) e' e
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
  FillLEnvLow-<ExpLow {ε} {e} {e'} fill1 fill2 (<ExpLow= eq lt) = <ExpLow= eq' fill'
    where 
    eq' : surface-news-low e' ≡ surface-news-low e
    eq' 
      rewrite FillLEnvLow-surface fill1 
      rewrite FillLEnvLow-surface fill2 
      rewrite eq
      = refl
    fill' : <Low (SkelLow e') e' e
    fill' rewrite sym (skel-ll-comm fill1) = FillLEnvLow-<Low fill1 fill2 lt 

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
  FillUEnvLow-<ExpLow {ε} {e} {e'} fill1 fill2 (<ExpUp= eq lt) = <ExpLow= eq' fill'
    where 
    eq' : surface-news-low e' ≡ surface-news-low e
    eq' 
      rewrite FillUEnvLow-surface fill1 
      rewrite FillUEnvLow-surface fill2 
      rewrite eq
      = refl
    fill' : <Low (SkelLow e') e' e 
    fill' rewrite sym (skel-ul-comm fill1) = FillUEnvLow-<Low fill1 fill2 lt 
  
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
      (s : Skeleton) ->
      Acc (<Mid s) e ->
      ∀ {e'} ->
      (<Up s e' (e ⇒ (t , Old))) -> 
      (Acc (<Up s) e')
    translate-acc-up-old' s (acc ac) (<Upper x) = translate-acc-up s (ac x)
    
    translate-acc-up-old : ∀{e t} ->
      (s : Skeleton) ->
      Acc (<Mid s) e ->
      Acc (<Up s) (e ⇒ (t , Old))
    translate-acc-up-old s ac = acc (translate-acc-up-old' s ac)

    translate-acc-up' : ∀{e syn} ->
      (s : Skeleton) ->
      Acc (<Mid s) e ->
      ∀ {e'} ->
      (<Up s e' (e ⇒ syn)) -> 
      (Acc (<Up s) e') 
    translate-acc-up' s ac (<Upper= <NewC) = translate-acc-up-old s ac
    translate-acc-up' s (acc ac) (<Upper x) = translate-acc-up s (ac x)

    translate-acc-up : ∀{e syn} ->
      (s : Skeleton) ->
      Acc (<Mid s) e ->
      Acc (<Up s) (e ⇒ syn)
    translate-acc-up s ac = acc (translate-acc-up' s ac)
  
  mutual

    translate-acc-low-old' : ∀{e m t} ->
      (s : Skeleton) ->
      Acc (<Up s) e ->
      ∀ {e'} ->
      (<Low s e' (e [ m ]⇐ (t , Old))) -> 
      (Acc (<Low s) e') 
    translate-acc-low-old' s (acc ac) (<Lower= =NewOld lt) = translate-acc-low-old s (ac lt)

    translate-acc-low-old : ∀{e m t} ->
      (s : Skeleton) ->
      Acc (<Up s) e ->
      Acc (<Low s) (e [ m ]⇐ (t , Old))
    translate-acc-low-old s ac = acc (translate-acc-low-old' s ac)

  mutual

    translate-acc-low'' : ∀{e m ana} ->
      (s : Skeleton) ->
      WellFounded (<Up s) ->
      (Acc (<Up s) e) -> 
      ∀ {e'} ->
      (<Low s e' (e [ m ]⇐ ana)) -> 
      (Acc (<Low s) e') 
    translate-acc-low'' s wf ac (<Lower <NewC) = translate-acc-low-old s (wf _)
    translate-acc-low'' s wf (acc rs) (<Lower= eq lt) = translate-acc-low' s wf (rs lt)

    translate-acc-low' : ∀{e m ana} ->
      (s : Skeleton) ->
      WellFounded (<Up s) ->
      (Acc (<Up s) e) -> 
      Acc (<Low s) (e [ m ]⇐ ana)
    translate-acc-low' s wf ac = acc (translate-acc-low'' s wf ac)
    
    translate-acc-low : ∀{e m ana} ->
      (s : Skeleton) ->
      WellFounded (<Up s) ->
      Acc (<Low s) (e [ m ]⇐ ana)
    translate-acc-low s wf = translate-acc-low' s wf (wf _)
    
  mutual 

    translate-acc-asc' : ∀ {a e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      ∀ {e'} ->
      (<Mid (S1 s) e' (EAsc a e)) -> 
      (Acc (<Mid (S1 s)) e') 
    translate-acc-asc' s (acc ac) (<Asc x) = translate-acc-asc s (ac x)
     
    translate-acc-asc : ∀ {a e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      Acc (<Mid (S1 s)) (EAsc a e)
    translate-acc-asc s ac = acc (translate-acc-asc' s ac)   

  mutual 

    translate-acc-fun' : ∀ {a1 a2 a3 a4 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      ∀ {e'} ->
      (<Mid (S1 s) e' (EFun a1 a2 a3 a4 e)) -> 
      (Acc (<Mid (S1 s)) e') 
    translate-acc-fun' s (acc ac) (<Fun x) = translate-acc-fun s (ac x)
     
    translate-acc-fun : ∀ {a1 a2 a3 a4 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      Acc (<Mid (S1 s)) (EFun a1 a2 a3 a4 e)
    translate-acc-fun s ac = acc (translate-acc-fun' s ac)

  mutual 

    translate-acc-ap'' : ∀ {e1 e2 a} ->
      (s1 s2 : Skeleton) ->
      WellFounded (<Low s1) ->
      WellFounded (<Low s2) ->
      Acc (<Low s1) e1 ->
      Acc (<Low s2) e2 ->
      ∀ {e'} ->
      (<Mid (S2 s1 s2) e' (EAp e1 a e2)) -> 
      (Acc (<Mid (S2 s1 s2)) e') 
    translate-acc-ap'' s1 s2 wf1 wf2 (acc ac1) ac2 (<Ap< lt) = translate-acc-ap' s1 s2 wf1 wf2 (ac1 lt) (wf2 _)
    translate-acc-ap'' s1 s2 wf1 wf2 ac1 (acc ac2) (<Ap=< lt) = translate-acc-ap' s1 s2 wf1 wf2 ac1 (ac2 lt)

    translate-acc-ap' : ∀ {e1 e2 a} ->
      (s1 s2 : Skeleton) ->
      WellFounded (<Low s1) ->
      WellFounded (<Low s2) ->
      Acc (<Low s1) e1 ->
      Acc (<Low s2) e2 ->
      Acc (<Mid (S2 s1 s2)) (EAp e1 a e2)
    translate-acc-ap' s1 s2 wf1 wf2 ac1 ac2 = acc (translate-acc-ap'' s1 s2 wf1 wf2 ac1 ac2)

    translate-acc-ap : ∀ {e1 e2 a} ->
      (s1 s2 : Skeleton) ->
      WellFounded (<Low s1) ->
      WellFounded (<Low s2) ->
      Acc (<Mid (S2 s1 s2)) (EAp e1 a e2)
    translate-acc-ap s1 s2 wf1 wf2 = translate-acc-ap' s1 s2 wf1 wf2 (wf1 _) (wf2 _) 

  mutual 
    
    <Up-wf-old' : 
      (s : Skeleton) ->
      (e : ExpMid) -> 
      {t : Data} -> 
      ∀ {e'} ->
      (<Up s e' (e ⇒ (t , Old))) -> 
      (Acc (<Up s) e') 
    <Up-wf-old' s e (<Upper lt) = translate-acc-up s (<Mid-wf' s _ lt)

    <Up-wf-old : 
      (s : Skeleton) ->
      (e : ExpMid) -> 
      {t : Data} -> 
      (Acc (<Up s) (e ⇒ (t , Old))) 
    <Up-wf-old s e = acc (<Up-wf-old' s e)

    <Up-wf' : 
      (s : Skeleton) ->
      (e : ExpUp) -> 
      ∀ {e'} ->
      (<Up s e' e) -> 
      (Acc (<Up s) e') 
    <Up-wf' s (e ⇒ _) (<Upper= <NewC) = <Up-wf-old s e
    <Up-wf' s e (<Upper lt) = translate-acc-up s (<Mid-wf s _)
    
    <Up-wf : (s : Skeleton) -> WellFounded (<Up s)
    <Up-wf s e = acc (<Up-wf' s e)

    <Mid-wf' : 
      (s : Skeleton) ->
      (e : ExpMid) -> 
      ∀ {e'} ->
      (<Mid s e' e) -> 
      (Acc (<Mid s) e') 
    <Mid-wf' s EConst ()
    <Mid-wf' s EHole ()
    <Mid-wf' s (EVar _ _) ()
    <Mid-wf' (S1 s) (EAsc _ e) (<Asc lt) = translate-acc-asc s (<Low-wf' s e lt)
    <Mid-wf' (S1 s) (EFun _ _ _ _ e) (<Fun lt) = translate-acc-fun s (<Low-wf' s e lt)
    <Mid-wf' (S2 s1 s2) (EAp e1 _ e2) (<Ap< {e1 = e3} {e4} lt) with <Low-wf s2
    ... | weird = translate-acc-ap s1 s2 (<Low-wf s1) weird
    <Mid-wf' (S2 s1 s2) (EAp e1 _ e2) (<Ap=< lt) = translate-acc-ap s1 s2 (<Low-wf s1) (<Low-wf s2)

    <Mid-wf : (s : Skeleton) -> WellFounded (<Mid s)
    <Mid-wf s e = acc (<Mid-wf' s e)

    <Low-wf' : 
      (s : Skeleton) ->
      (e : ExpLow) -> 
      ∀ {e'} ->
      (<Low s e' e) -> 
      (Acc (<Low s) e') 
    <Low-wf' s e {x [ x₁ ]⇐ x₂} lt = translate-acc-low s (<Up-wf s)

    <Low-wf : (s : Skeleton) -> WellFounded (<Low s)
    <Low-wf s e = acc (<Low-wf' s e)

  -- <Surface : Program -> Program 
  
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

    -- <Program-wf-3' : 
    --   (p : Program) -> 
    --   (n : ℕ) -> 
    --   (surface-news-low (ExpLowOfProgram p) ≡ n) ->
    --   ∀ {p'} ->
    --   (surface-news-low (ExpLowOfProgram p') <
    --   surface-news-low (ExpLowOfProgram p)) -> 
    --   (Acc <Program p')
    -- <Program-wf-3' = {!   !}
    
    -- <Program-wf-3 : 
    --   (p : Program) -> 
    --   (n : ℕ) -> 
    --   (surface-news-low (ExpLowOfProgram p) ≡ n) ->
    --   (Acc <Program p)
    -- <Program-wf-3 p n eq = acc {! <Program-wf-3' p n eq  !}

  <Program-wf'' : 
    (p : Program) -> 
    Acc (<Low (SkelProgram p)) (ExpLowOfProgram p) ->
    ∀ {p'} ->
    (<Program p' p) -> 
    (Acc <Program p') 
  <Program-wf'' p ac (<Program< lt) = {!   !} --<Program-wf-2 p _ refl lt
  <Program-wf'' p acs (<Program= eq lt) = {!   !} --<Program-wf'' _ (rs {!   !}) {!   !}

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

  -- ↤P-wf' :
  --   (p : Program) -> 
  --   ∀ {p'} -> 
  --   p' ↤P p -> 
  --   (Acc _↤P_ p') 
  -- ↤P-wf' p step = acc-translate (<Program-wf _)

  -- ↤P-wf : WellFounded _↤P_
  -- ↤P-wf p = acc (↤P-wf' p)

  -- data _P↦*_ : Program -> Program -> Set where 
  --   P↦0 : ∀ {p} ->
  --     p P↦* p
  --   P↦suc : ∀ {p p' p''} ->
  --     p P↦ p' -> 
  --     p' P↦* p'' ->
  --     p P↦* p''

  -- TerminationProgramRec : 
  --   {p : Program} ->
  --   (Acc _↤P_ p) ->
  --   (WellTypedProgram p) ->
  --   ∃[ p' ] (p P↦* p') × (SettledProgram p')
  -- TerminationProgramRec {p} (acc recursor) wt with settled-dec p | ProgressProgram wt 
  -- ... | Inl settled | _ = p , P↦0 , settled
  -- ... | Inr unsettled | Inr settled = ⊥-elim (unsettled settled)
  -- ... | Inr unsettled | Inl (p' , step) with TerminationProgramRec {p'} (recursor step) (PreservationProgram wt step)
  -- ... | p'' , steps , settled = p'' , P↦suc step steps , settled
 
  -- TerminationProgram : 
  --   {p : Program} ->
  --   (WellTypedProgram p) ->
  --   ∃[ p' ] (p P↦* p') × (SettledProgram p')
  -- TerminationProgram wt = TerminationProgramRec (↤P-wf _) wt
        