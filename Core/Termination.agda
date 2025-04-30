open import Data.Nat 
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Product
open import Relation.Binary.PropositionalEquality 
open import Induction.WellFounded 

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.VariableUpdate
open import Core.Update

module Core.Termination where

  new-number : Dirtiness -> ℕ 
  new-number • = 0
  new-number ★ = 1

  mutual 
    
    surface-dirties-up : SynExp -> ℕ
    surface-dirties-up (e ⇒ _) = surface-dirties-mid e

    surface-dirties-mid : ConExp -> ℕ
    surface-dirties-mid (EConst) = 0
    surface-dirties-mid (EHole) = 0
    surface-dirties-mid (EVar _ _) = 0
    surface-dirties-mid (EAsc (_ , n-asc) e-body) = (new-number n-asc) + surface-dirties-low e-body
    surface-dirties-mid (EFun _ (_ , n-ann) _ _ e-body) = (new-number n-ann) + surface-dirties-low e-body
    surface-dirties-mid (EAp e-fun _ e-arg) = surface-dirties-low e-fun + surface-dirties-low e-arg
    surface-dirties-mid (EPair e-fst e-snd _) = surface-dirties-low e-fst + surface-dirties-low e-snd
    surface-dirties-mid (EProj _ e _) = surface-dirties-low e
    surface-dirties-mid (ETypFun _ _ e) = surface-dirties-low e
    surface-dirties-mid (ETypAp e _ (_ , n-arg)) = (new-number n-arg) + surface-dirties-low e

    surface-dirties-low : AnaExp -> ℕ
    surface-dirties-low (e [ _ ]⇐ _) = surface-dirties-up e

  data =★ : ○Data -> ○Data -> Set where 
    =★• : ∀ {t1 t2} ->
      =★ (t1 , •) (t2 , •)
    =★★ : ∀ {t1 t2} ->
      =★ (t1 , ★) (t2 , ★)

  =★-refl : ∀ {n} -> =★ n n 
  =★-refl {_ , •} = =★•
  =★-refl {_ , ★} = =★★

  data <★ : ○Data -> ○Data -> Set where 
    <★C : ∀ {t1 t2} ->
      <★ (t1 , •) (t2 , ★)

  data Skeleton : Set where 
    S0 : Skeleton 
    S1 : Skeleton -> Skeleton 
    S2 : Skeleton -> Skeleton -> Skeleton 

  mutual 

    SkelUp : SynExp -> Skeleton 
    SkelUp (e ⇒ _) = SkelMid e

    SkelMid : ConExp -> Skeleton 
    SkelMid EConst = S0
    SkelMid EHole = S0
    SkelMid (EVar _ _) = S0
    SkelMid (EAsc _ e) = S1 (SkelLow e)
    SkelMid (EFun _ _ _ _ e) = S1 (SkelLow e)
    SkelMid (EProj _ e _) = S1 (SkelLow e)
    SkelMid (EAp e1 _ e2) = S2 (SkelLow e1) (SkelLow e2)
    SkelMid (EPair e1 e2 _) = S2 (SkelLow e1) (SkelLow e2)
    SkelMid (ETypFun _ _ e) = S1 (SkelLow e)
    SkelMid (ETypAp e _ _) = S1 (SkelLow e)

    SkelLow : AnaExp -> Skeleton  
    SkelLow (e [ _ ]⇐ _) = SkelUp e

  SkelProgram : Program -> Skeleton 
  SkelProgram p = SkelLow (AnaExpOfProgram p)

  mutual 

    data <Up : Skeleton -> SynExp -> SynExp -> Set where 
      <Upper : ∀ {s e1 e2 syn1 syn2} ->
        <Mid s e1 e2 ->  
        <Up s (e1 ⇒ syn1) (e2 ⇒ syn2)
      <Upper= : ∀ {e syn1 syn2} ->
        <★ syn1 syn2 ->  
        <Up (SkelMid e) (e ⇒ syn1) (e ⇒ syn2)
      
    data <Mid : Skeleton -> ConExp -> ConExp -> Set where 
      <Asc : ∀ {s a1 a2 e1 e2} ->
        <Low s e1 e2 -> 
        <Mid (S1 s) (EAsc a1 e1) (EAsc a2 e2)
      <Fun : ∀ {s a1 a2 a3 a4 a5 a6 a7 a8 e1 e2} ->
        <Low s e1 e2 -> 
        <Mid (S1 s) (EFun a1 a2 a3 a4 e1) (EFun a5 a6 a7 a8 e2)
      <Proj : ∀ {s a1 a2 a3 a4 e1 e2} ->
        <Low s e1 e2 -> 
        <Mid (S1 s) (EProj a1 e1 a2) (EProj a3 e2 a4)
      <Ap< : ∀ {s1 a1 a2 e1 e2 e3 e4} ->
        <Low s1 e1 e3 -> 
        (SkelLow e2) ≡ (SkelLow e4) ->
        <Mid (S2 s1 (SkelLow e2)) (EAp e1 a1 e2) (EAp e3 a2 e4)
      <Ap=< : ∀ {s2 a1 a2 e1 e2 e3} ->
        <Low s2 e2 e3 -> 
        <Mid (S2 (SkelLow e1) s2) (EAp e1 a1 e2) (EAp e1 a2 e3)
      <Pair< : ∀ {s1 a1 a2 e1 e2 e3 e4} ->
        <Low s1 e1 e3 -> 
        (SkelLow e2) ≡ (SkelLow e4) ->
        <Mid (S2 s1 (SkelLow e2)) (EPair e1 e2 a1) (EPair e3 e4 a2)
      <Pair=< : ∀ {s2 a1 a2 e1 e2 e3} ->
        <Low s2 e2 e3 -> 
        <Mid (S2 (SkelLow e1) s2) (EPair e1 e2 a1) (EPair e1 e3 a2)
      <TypFun : ∀ {s a1 a2 a3 a4 e1 e2} ->
        <Low s e1 e2 -> 
        <Mid (S1 s) (ETypFun a1 a2 e1) (ETypFun a3 a4 e2)
      <TypAp : ∀ {s a1 a2 a3 a4 e1 e2} ->
        <Low s e1 e2 -> 
        <Mid (S1 s) (ETypAp e1 a1 a2) (ETypAp e2 a3 a4)

    data <Low : Skeleton -> AnaExp -> AnaExp -> Set where 
      <Lower : ∀ {e1 e2 a1 a2 ana1 ana2} ->
        <★ ana1 ana2 ->  
        (SkelUp e1) ≡ (SkelUp e2) ->
        <Low (SkelUp e1) (e1 [ a1 ]⇐ ana1) (e2 [ a2 ]⇐ ana2)
      <Lower= : ∀ {s e1 e2 a1 a2 ana1 ana2} ->
        =★ ana1 ana2 ->  
        <Up s e1 e2 ->
        <Low s (e1 [ a1 ]⇐ ana1) (e2 [ a2 ]⇐ ana2)

  data <Program : Program -> Program -> Set where 
    <Program< : ∀ {p p'} ->
      surface-dirties-low (AnaExpOfProgram p) < surface-dirties-low (AnaExpOfProgram p') -> 
      <Program p p'
    <Program= : ∀ {p p'} ->
      surface-dirties-low (AnaExpOfProgram p) ≡ surface-dirties-low (AnaExpOfProgram p') -> 
      <Low (SkelProgram p) (AnaExpOfProgram p) (AnaExpOfProgram p') ->
      <Program p p'

  data <SynExp : SynExp -> SynExp -> Set where 
    <SynExp< : ∀ {e e'} ->
      surface-dirties-up e < surface-dirties-up e' -> 
      <SynExp e e'
    <SynExp= : ∀ {e e'} ->
      surface-dirties-up e ≡ surface-dirties-up e' -> 
      <Up (SkelUp e) e e' ->
      <SynExp e e'

  data <AnaExp : AnaExp -> AnaExp -> Set where 
    <AnaExp< : ∀ {e e'} ->
      surface-dirties-low e < surface-dirties-low e' -> 
      <AnaExp e e'
    <AnaExp= : ∀ {e e'} ->
      surface-dirties-low e ≡ surface-dirties-low e' -> 
      <Low (SkelLow e) e e' ->
      <AnaExp e e'

  mutual 

    <Up-skel : ∀{s e1 e2} -> 
      <Up s e1 e2 -> 
      (s ≡ (SkelUp e2))
    <Up-skel (<Upper lt) = <Mid-skel lt
    <Up-skel (<Upper= _) = refl

    <Mid-skel : ∀{s e1 e2} -> 
      <Mid s e1 e2 -> 
      (s ≡ (SkelMid e2))
    <Mid-skel (<Asc x) rewrite (<Low-skel x) = refl
    <Mid-skel (<Fun x) rewrite (<Low-skel x) = refl
    <Mid-skel (<Proj x) rewrite (<Low-skel x) = refl
    <Mid-skel (<Ap< x eq) rewrite (<Low-skel x) rewrite eq = refl
    <Mid-skel (<Ap=< x) rewrite (<Low-skel x) = refl
    <Mid-skel (<Pair< x eq) rewrite (<Low-skel x) rewrite eq = refl
    <Mid-skel (<Pair=< x) rewrite (<Low-skel x) = refl
    <Mid-skel (<TypFun x) rewrite (<Low-skel x) = refl
    <Mid-skel (<TypAp x) rewrite (<Low-skel x) = refl
    
    <Low-skel : ∀{s e1 e2} -> 
      <Low s e1 e2 -> 
      (s ≡ (SkelLow e2))
    <Low-skel (<Lower _ eq) = eq
    <Low-skel (<Lower= _ lt) = <Up-skel lt

  var-update-preserves-surface-dirties : ∀{x t m e e'} ->
    VariableUpdate x t m e e' ->
    surface-dirties-up e ≡ surface-dirties-up e'
  var-update-preserves-surface-dirties VUConst = refl
  var-update-preserves-surface-dirties VUHole = refl
  var-update-preserves-surface-dirties VUVarEq = refl
  var-update-preserves-surface-dirties (VUVarNeq _) = refl
  var-update-preserves-surface-dirties VUFunEq = refl
  var-update-preserves-surface-dirties (VUFunNeq _ var-update) 
    rewrite var-update-preserves-surface-dirties var-update = refl
  var-update-preserves-surface-dirties (VUAsc var-update) 
    rewrite var-update-preserves-surface-dirties var-update = refl
  var-update-preserves-surface-dirties (VUProj var-update) 
    rewrite var-update-preserves-surface-dirties var-update = refl
  var-update-preserves-surface-dirties (VUAp var-update1 var-update2) 
    rewrite var-update-preserves-surface-dirties var-update1
    rewrite var-update-preserves-surface-dirties var-update2 = refl
  var-update-preserves-surface-dirties (VUPair var-update1 var-update2) 
    rewrite var-update-preserves-surface-dirties var-update1
    rewrite var-update-preserves-surface-dirties var-update2 = refl
  var-update-preserves-surface-dirties (VUTypFun var-update) 
    rewrite var-update-preserves-surface-dirties var-update = refl
  var-update-preserves-surface-dirties (VUTypAp var-update) 
    rewrite var-update-preserves-surface-dirties var-update = refl

  var-update?-preserves-surface-dirties : ∀{x t m e e'} ->
    VariableUpdate? x t m e e' ->
    surface-dirties-up e ≡ surface-dirties-up e'
  var-update?-preserves-surface-dirties {BHole} refl = refl
  var-update?-preserves-surface-dirties {BVar x} = var-update-preserves-surface-dirties

  StepDecreaseU : ∀ {e e'} ->
    e s↦ e' -> 
    <SynExp e' e
  StepDecreaseU StepAsc = <SynExp< (n<1+n _)
  StepDecreaseU (StepAp x) = <SynExp= refl (<Upper (<Ap< (<Lower= =★-refl (<Upper= <★C)) refl))
  StepDecreaseU (StepProj x) = <SynExp= refl (<Upper (<Proj (<Lower= =★-refl (<Upper= <★C))))
  StepDecreaseU (StepTypApFun x x₁) = <SynExp= refl (<Upper (<TypAp (<Lower= =★-refl (<Upper= <★C))))
  StepDecreaseU (StepTypApArg x x₁) = <SynExp< (n<1+n _)

  StepDecreaseL : ∀ {e e'} ->
    e a↦ e' -> 
    <AnaExp e' e
  StepDecreaseL (StepAnnFun {e-body = e ⇒ _} {e-body' = e' ⇒ _} var-update) = <AnaExp< helper
    where 
    helper : surface-dirties-mid e' < suc (surface-dirties-mid e)
    helper rewrite (var-update?-preserves-surface-dirties var-update) = ≤-refl
  StepDecreaseL (StepSyn x) = <AnaExp= refl (<Lower= =★-refl (<Upper= <★C))
  StepDecreaseL (StepAna x x₁) = <AnaExp= refl (<Lower <★C refl)
  StepDecreaseL (StepAnaFun x x₁) = <AnaExp= refl (<Lower <★C refl)
  StepDecreaseL StepSynFun = <AnaExp= refl (<Lower= =★-refl (<Upper (<Fun (<Lower= =★-refl (<Upper= <★C)))))
  StepDecreaseL (StepAnaPair x) = <AnaExp= refl (<Lower <★C refl)
  StepDecreaseL StepSynPairFst = <AnaExp= refl (<Lower= =★-refl (<Upper (<Pair< (<Lower= =★-refl (<Upper= <★C)) refl)))
  StepDecreaseL StepSynPairSnd = <AnaExp= refl (<Lower= =★-refl (<Upper (<Pair=< (<Lower= =★-refl (<Upper= <★C)))))
  StepDecreaseL (StepAnaTypFun x) = <AnaExp= refl (<Lower <★C refl)
  StepDecreaseL StepSynTypFun = <AnaExp= refl (<Lower= =★-refl (<Upper (<TypFun (<Lower= =★-refl (<Upper= <★C)))))

  mutual 
    
    surface-dirties-uu : SynEnvSyn -> ℕ
    surface-dirties-uu S⊙ = 0
    surface-dirties-uu (SynEnvSynRec ε _) = surface-dirties-um ε

    surface-dirties-um : SynEnvCon -> ℕ
    surface-dirties-um (SynEnvAsc (_ , n-asc) ε) = (new-number n-asc) + surface-dirties-ul ε
    surface-dirties-um (SynEnvFun _ (_ , n-ann) _ _ ε) = (new-number n-ann) + surface-dirties-ul ε
    surface-dirties-um (SynEnvProj _ ε _) = surface-dirties-ul ε
    surface-dirties-um (SynEnvAp1 ε _ e-arg) = surface-dirties-ul ε + surface-dirties-low e-arg
    surface-dirties-um (SynEnvAp2 e-fun _ ε) = surface-dirties-low e-fun + surface-dirties-ul ε
    surface-dirties-um (SynEnvPair1 ε e-snd _) = surface-dirties-ul ε + surface-dirties-low e-snd
    surface-dirties-um (SynEnvPair2 e-fst ε _) = surface-dirties-low e-fst + surface-dirties-ul ε
    surface-dirties-um (SynEnvTypFun _ _ ε) = surface-dirties-ul ε
    surface-dirties-um (SynEnvTypAp ε _ (_ , n-arg)) = (new-number n-arg) + surface-dirties-ul ε

    surface-dirties-ul : SynEnvAna -> ℕ
    surface-dirties-ul (SynEnvAnaRec ε _ _) = surface-dirties-uu ε

  mutual

    surface-dirties-lu : AnaEnvSyn -> ℕ
    surface-dirties-lu (AnaEnvSynRec ε _) = surface-dirties-lm ε

    surface-dirties-lm : AnaEnvCon -> ℕ
    surface-dirties-lm (AnaEnvAsc (_ , n-asc) ε) = (new-number n-asc) + surface-dirties-ll ε
    surface-dirties-lm (AnaEnvFun _ (_ , n-ann) _ _ ε) = (new-number n-ann) + surface-dirties-ll ε
    surface-dirties-lm (AnaEnvProj _ ε _) = surface-dirties-ll ε
    surface-dirties-lm (AnaEnvAp1 ε _ e-arg) = surface-dirties-ll ε + surface-dirties-low e-arg
    surface-dirties-lm (AnaEnvAp2 e-fun _ ε) = surface-dirties-low e-fun + surface-dirties-ll ε
    surface-dirties-lm (AnaEnvPair1 ε e-snd _) = surface-dirties-ll ε + surface-dirties-low e-snd
    surface-dirties-lm (AnaEnvPair2 e-fst ε _) = surface-dirties-low e-fst + surface-dirties-ll ε
    surface-dirties-lm (AnaEnvTypFun _ _ ε) = surface-dirties-ll ε
    surface-dirties-lm (AnaEnvTypAp ε _ (_ , n-arg)) = (new-number n-arg) + surface-dirties-ll ε

    surface-dirties-ll : AnaEnvAna -> ℕ
    surface-dirties-ll A⊙ = 0
    surface-dirties-ll (AnaEnvAnaRec ε _ _) = surface-dirties-lu ε

  mutual 

    FillSynEnvSyn-surface : ∀ {ε e e-in} ->
      ε S⟦ e-in ⟧S≡ e ->
      surface-dirties-up e ≡ surface-dirties-uu ε + surface-dirties-up e-in
    FillSynEnvSyn-surface FillS⊙ = refl
    FillSynEnvSyn-surface (FillSynEnvSynRec fill) = FillSynEnvCon-surface fill

    FillSynEnvCon-surface : ∀ {ε e e-in} ->
      ε S⟦ e-in ⟧C≡ e ->
      surface-dirties-mid e ≡ surface-dirties-um ε + surface-dirties-up e-in 
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvAsc {ε = ε} {t = (_ , n)} fill) 
      rewrite FillSynEnvAna-surface fill 
      =  sym (+-assoc (new-number n) (surface-dirties-ul ε) (surface-dirties-up e-in))
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvFun {ε = ε} {t = (_ , n)} fill) 
      rewrite FillSynEnvAna-surface fill 
      = sym (+-assoc (new-number n) (surface-dirties-ul ε) (surface-dirties-up e-in))
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvProj {ε = ε} fill) 
      rewrite FillSynEnvAna-surface fill 
      = refl
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvAp1 {ε = ε} {e2 = e2} fill) 
      rewrite FillSynEnvAna-surface fill 
      rewrite (+-assoc (surface-dirties-ul ε) (surface-dirties-up e-in) (surface-dirties-low e2))
      rewrite +-comm (surface-dirties-up e-in) (surface-dirties-low e2) 
      rewrite sym (+-assoc (surface-dirties-ul ε) (surface-dirties-low e2) (surface-dirties-up e-in))
      = refl
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvAp2 {ε = ε} {e1 = e1} fill) 
      rewrite FillSynEnvAna-surface fill 
      = sym (+-assoc (surface-dirties-low e1) (surface-dirties-ul ε) (surface-dirties-up e-in))
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvPair1 {ε = ε} {e2 = e2} fill) 
      rewrite FillSynEnvAna-surface fill 
      rewrite (+-assoc (surface-dirties-ul ε) (surface-dirties-up e-in) (surface-dirties-low e2))
      rewrite +-comm (surface-dirties-up e-in) (surface-dirties-low e2) 
      rewrite sym (+-assoc (surface-dirties-ul ε) (surface-dirties-low e2) (surface-dirties-up e-in))
      = refl
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvPair2 {ε = ε} {e1 = e1} fill) 
      rewrite FillSynEnvAna-surface fill 
      = sym (+-assoc (surface-dirties-low e1) (surface-dirties-ul ε) (surface-dirties-up e-in))
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvTypFun {ε = ε} fill) 
      rewrite FillSynEnvAna-surface fill 
      = refl
    FillSynEnvCon-surface {e-in = e-in} (FillSynEnvTypAp {ε = ε} {t = (_ , n)} fill) 
      rewrite FillSynEnvAna-surface fill 
      = sym (+-assoc (new-number n) (surface-dirties-ul ε) (surface-dirties-up e-in))

    FillSynEnvAna-surface : ∀ {ε e e-in} ->
      ε S⟦ e-in ⟧A≡ e ->
      surface-dirties-low e ≡ surface-dirties-ul ε + surface-dirties-up e-in
    FillSynEnvAna-surface (FillSynEnvAnaRec fill) = FillSynEnvSyn-surface fill

  mutual 

    FillAnaEnvSyn-surface : ∀ {ε e e-in} ->
      ε A⟦ e-in ⟧S≡ e ->
      surface-dirties-up e ≡ surface-dirties-lu ε + surface-dirties-low e-in
    FillAnaEnvSyn-surface (FillAnaEnvSynRec fill) = FillAnaEnvCon-surface fill

    FillAnaEnvCon-surface : ∀ {ε e e-in} ->
      ε A⟦ e-in ⟧C≡ e ->
      surface-dirties-mid e ≡ surface-dirties-lm ε + surface-dirties-low e-in 
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvAsc {ε = ε} {t = (_ , n)} fill) 
      rewrite FillAnaEnvAna-surface fill 
      =  sym (+-assoc (new-number n) (surface-dirties-ll ε) (surface-dirties-low e-in))
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvFun {ε = ε} {t = (_ , n)} fill) 
      rewrite FillAnaEnvAna-surface fill 
      = sym (+-assoc (new-number n) (surface-dirties-ll ε) (surface-dirties-low e-in))
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvProj {ε = ε} fill) 
      rewrite FillAnaEnvAna-surface fill 
      = refl
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvAp1 {ε = ε} {e2 = e2} fill) 
      rewrite FillAnaEnvAna-surface fill 
      rewrite (+-assoc (surface-dirties-ll ε) (surface-dirties-low e-in) (surface-dirties-low e2))
      rewrite +-comm (surface-dirties-low e-in) (surface-dirties-low e2) 
      rewrite sym (+-assoc (surface-dirties-ll ε) (surface-dirties-low e2) (surface-dirties-low e-in))
      = refl
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvAp2 {ε = ε} {e1 = e1} fill) 
      rewrite FillAnaEnvAna-surface fill 
      = sym (+-assoc (surface-dirties-low e1) (surface-dirties-ll ε) (surface-dirties-low e-in))
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvPair1 {ε = ε} {e2 = e2} fill) 
      rewrite FillAnaEnvAna-surface fill 
      rewrite (+-assoc (surface-dirties-ll ε) (surface-dirties-low e-in) (surface-dirties-low e2))
      rewrite +-comm (surface-dirties-low e-in) (surface-dirties-low e2) 
      rewrite sym (+-assoc (surface-dirties-ll ε) (surface-dirties-low e2) (surface-dirties-low e-in))
      = refl
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvPair2 {ε = ε} {e1 = e1} fill) 
      rewrite FillAnaEnvAna-surface fill 
      = sym (+-assoc (surface-dirties-low e1) (surface-dirties-ll ε) (surface-dirties-low e-in))
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvTypFun {ε = ε} fill) 
      rewrite FillAnaEnvAna-surface fill 
      = refl
    FillAnaEnvCon-surface {e-in = e-in} (FillAnaEnvTypAp {ε = ε} {t = (_ , n)} fill) 
      rewrite FillAnaEnvAna-surface fill 
      = sym (+-assoc (new-number n) (surface-dirties-ll ε) (surface-dirties-low e-in))

    FillAnaEnvAna-surface : ∀ {ε e e-in} ->
      ε A⟦ e-in ⟧A≡ e ->
      surface-dirties-low e ≡ surface-dirties-ll ε + surface-dirties-low e-in
    FillAnaEnvAna-surface FillA⊙ = refl
    FillAnaEnvAna-surface (FillAnaEnvAnaRec fill) = FillAnaEnvSyn-surface fill 

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

    skel-lu : AnaEnvSyn -> SkelEnv 
    skel-lu (AnaEnvSynRec e _) = skel-lm e

    skel-lm : AnaEnvCon -> SkelEnv 
    skel-lm (AnaEnvAsc _ e) = SE1 (skel-ll e)
    skel-lm (AnaEnvFun _ _ _ _ e) = SE1 (skel-ll e)
    skel-lm (AnaEnvProj _ e _) = SE1 (skel-ll e)
    skel-lm (AnaEnvAp1 e1 _ e2) = SEL (skel-ll e1) (SkelLow e2)
    skel-lm (AnaEnvAp2 e1 _ e2) = SER (SkelLow e1) (skel-ll e2)
    skel-lm (AnaEnvPair1 e1 e2 _) = SEL (skel-ll e1) (SkelLow e2)
    skel-lm (AnaEnvPair2 e1 e2 _) = SER (SkelLow e1) (skel-ll e2)
    skel-lm (AnaEnvTypFun _ _ e) = SE1 (skel-ll e)
    skel-lm (AnaEnvTypAp e _ _) = SE1 (skel-ll e)

    skel-ll : AnaEnvAna -> SkelEnv 
    skel-ll A⊙ = S⊙
    skel-ll (AnaEnvAnaRec e _ _) = skel-lu e

  mutual 

    skel-uu : SynEnvSyn -> SkelEnv 
    skel-uu S⊙ = S⊙
    skel-uu (SynEnvSynRec e _) = skel-um e

    skel-um : SynEnvCon -> SkelEnv 
    skel-um (SynEnvAsc _ e) = SE1 (skel-ul e)
    skel-um (SynEnvFun _ _ _ _ e) = SE1 (skel-ul e)
    skel-um (SynEnvProj _ e _) = SE1 (skel-ul e)
    skel-um (SynEnvAp1 e1 _ e2) = SEL (skel-ul e1) (SkelLow e2)
    skel-um (SynEnvAp2 e1 _ e2) = SER (SkelLow e1) (skel-ul e2)
    skel-um (SynEnvPair1 e1 e2 _) = SEL (skel-ul e1) (SkelLow e2)
    skel-um (SynEnvPair2 e1 e2 _) = SER (SkelLow e1) (skel-ul e2)
    skel-um (SynEnvTypFun _ _ e) = SE1 (skel-ul e)
    skel-um (SynEnvTypAp e _ _) = SE1 (skel-ul e)

    skel-ul : SynEnvAna -> SkelEnv 
    skel-ul (SynEnvAnaRec e _ _) = skel-uu e

  mutual 

    skel-lu-comm : ∀ {ε e e-in} ->
      ε A⟦ e-in ⟧S≡ e ->
      SkelFill (SkelLow e-in) (skel-lu ε) ≡ SkelUp e
    skel-lu-comm (FillAnaEnvSynRec x) = skel-lm-comm x

    skel-lm-comm : ∀ {ε e e-in} ->
      ε A⟦ e-in ⟧C≡ e ->
      SkelFill (SkelLow e-in) (skel-lm ε) ≡ SkelMid e
    skel-lm-comm (FillAnaEnvFun x) = cong S1 (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvProj x) = cong S1 (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvAsc x) = cong S1 (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvAp1 {e2 = e2} x) = cong (λ a -> S2 a (SkelLow e2)) (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvAp2 {e1 = e1} x) = cong (S2 (SkelLow e1)) (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvPair1 {e2 = e2} x) = cong (λ a -> S2 a (SkelLow e2)) (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvPair2 {e1 = e1} x) = cong (S2 (SkelLow e1)) (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvTypFun x) = cong S1 (skel-ll-comm x)
    skel-lm-comm (FillAnaEnvTypAp x) = cong S1 (skel-ll-comm x)

    skel-ll-comm : ∀ {ε e e-in} ->
      ε A⟦ e-in ⟧A≡ e ->
      SkelFill (SkelLow e-in) (skel-ll ε) ≡ SkelLow e
    skel-ll-comm FillA⊙ = refl
    skel-ll-comm (FillAnaEnvAnaRec x) = skel-lu-comm x

  mutual 

    skel-uu-comm : ∀ {ε e e-in} ->
      ε S⟦ e-in ⟧S≡ e ->
      SkelFill (SkelUp e-in) (skel-uu ε) ≡ SkelUp e
    skel-uu-comm FillS⊙ = refl
    skel-uu-comm (FillSynEnvSynRec x) = skel-um-comm x

    skel-um-comm : ∀ {ε e e-in} ->
      ε S⟦ e-in ⟧C≡ e ->
      SkelFill (SkelUp e-in) (skel-um ε) ≡ SkelMid e
    skel-um-comm (FillSynEnvFun x) = cong S1 (skel-ul-comm x)
    skel-um-comm (FillSynEnvAsc x) = cong S1 (skel-ul-comm x)
    skel-um-comm (FillSynEnvProj x) = cong S1 (skel-ul-comm x)
    skel-um-comm (FillSynEnvAp1 {e2 = e2} x) = cong (λ a -> S2 a (SkelLow e2)) (skel-ul-comm x)
    skel-um-comm (FillSynEnvAp2 {e1 = e1} x) = cong (S2 (SkelLow e1)) (skel-ul-comm x)
    skel-um-comm (FillSynEnvPair1 {e2 = e2} x) = cong (λ a -> S2 a (SkelLow e2)) (skel-ul-comm x)
    skel-um-comm (FillSynEnvPair2 {e1 = e1} x) = cong (S2 (SkelLow e1)) (skel-ul-comm x)
    skel-um-comm (FillSynEnvTypFun x) = cong S1 (skel-ul-comm x)
    skel-um-comm (FillSynEnvTypAp x) = cong S1 (skel-ul-comm x)

    skel-ul-comm : ∀ {ε e e-in} ->
      ε S⟦ e-in ⟧A≡ e ->
      SkelFill (SkelUp e-in) (skel-ul ε) ≡ SkelLow e
    skel-ul-comm (FillSynEnvAnaRec x) = skel-uu-comm x

  mutual 

    FillAnaEnvSyn-<Up : ∀ {ε e e' e-in e-in' s} ->
      ε A⟦ e-in' ⟧S≡ e' ->
      ε A⟦ e-in ⟧S≡ e ->
      <Low s e-in' e-in ->
      <Up (SkelFill s (skel-lu ε)) e' e
    FillAnaEnvSyn-<Up (FillAnaEnvSynRec fill1) (FillAnaEnvSynRec fill2) lt = <Upper (FillAnaEnvCon-<Mid fill1 fill2 lt)

    FillAnaEnvCon-<Mid : ∀ {ε e e' e-in e-in' s} ->
      ε A⟦ e-in' ⟧C≡ e' ->
      ε A⟦ e-in ⟧C≡ e ->
      <Low s e-in' e-in ->
      <Mid (SkelFill s (skel-lm ε)) e' e
    FillAnaEnvCon-<Mid (FillAnaEnvAsc fill1) (FillAnaEnvAsc fill2) lt = <Asc (FillAnaEnvAna-<Low fill1 fill2 lt)
    FillAnaEnvCon-<Mid (FillAnaEnvFun fill1) (FillAnaEnvFun fill2) lt = <Fun (FillAnaEnvAna-<Low fill1 fill2 lt)
    FillAnaEnvCon-<Mid (FillAnaEnvProj fill1) (FillAnaEnvProj fill2) lt = <Proj (FillAnaEnvAna-<Low fill1 fill2 lt)
    FillAnaEnvCon-<Mid (FillAnaEnvAp1 fill1) (FillAnaEnvAp1 fill2) lt = <Ap< (FillAnaEnvAna-<Low fill1 fill2 lt) refl
    FillAnaEnvCon-<Mid (FillAnaEnvAp2 fill1) (FillAnaEnvAp2 fill2) lt = <Ap=< (FillAnaEnvAna-<Low fill1 fill2 lt)
    FillAnaEnvCon-<Mid (FillAnaEnvPair1 fill1) (FillAnaEnvPair1 fill2) lt = <Pair< (FillAnaEnvAna-<Low fill1 fill2 lt) refl
    FillAnaEnvCon-<Mid (FillAnaEnvPair2 fill1) (FillAnaEnvPair2 fill2) lt = <Pair=< (FillAnaEnvAna-<Low fill1 fill2 lt)
    FillAnaEnvCon-<Mid (FillAnaEnvTypFun fill1) (FillAnaEnvTypFun fill2) lt = <TypFun (FillAnaEnvAna-<Low fill1 fill2 lt)
    FillAnaEnvCon-<Mid (FillAnaEnvTypAp fill1) (FillAnaEnvTypAp fill2) lt = <TypAp (FillAnaEnvAna-<Low fill1 fill2 lt)

    FillAnaEnvAna-<Low : ∀ {ε e e' e-in e-in' s} ->
      ε A⟦ e-in' ⟧A≡ e' ->
      ε A⟦ e-in ⟧A≡ e ->
      <Low s e-in' e-in ->
      <Low (SkelFill s (skel-ll ε)) e' e
    FillAnaEnvAna-<Low FillA⊙ FillA⊙ lt = lt
    FillAnaEnvAna-<Low (FillAnaEnvAnaRec fill1) (FillAnaEnvAnaRec fill2) lt = <Lower= =★-refl (FillAnaEnvSyn-<Up fill1 fill2 lt)
  
  mutual 

    FillSynEnvSyn-<Up : ∀ {ε e e' e-in e-in' s} ->
      ε S⟦ e-in' ⟧S≡ e' ->
      ε S⟦ e-in ⟧S≡ e ->
      <Up s e-in' e-in ->
      <Up (SkelFill s (skel-uu ε)) e' e
    FillSynEnvSyn-<Up FillS⊙ FillS⊙ lt = lt
    FillSynEnvSyn-<Up (FillSynEnvSynRec fill1) (FillSynEnvSynRec fill2) lt = <Upper (FillSynEnvCon-<Mid fill1 fill2 lt)

    FillSynEnvCon-<Mid : ∀ {ε e e' e-in e-in' s} ->
      ε S⟦ e-in' ⟧C≡ e' ->
      ε S⟦ e-in ⟧C≡ e ->
      <Up s e-in' e-in ->
      <Mid (SkelFill s (skel-um ε)) e' e
    FillSynEnvCon-<Mid (FillSynEnvAsc fill1) (FillSynEnvAsc fill2) lt = <Asc (FillSynEnvAna-<Low fill1 fill2 lt)
    FillSynEnvCon-<Mid (FillSynEnvFun fill1) (FillSynEnvFun fill2) lt = <Fun (FillSynEnvAna-<Low fill1 fill2 lt)
    FillSynEnvCon-<Mid (FillSynEnvProj fill1) (FillSynEnvProj fill2) lt = <Proj (FillSynEnvAna-<Low fill1 fill2 lt)
    FillSynEnvCon-<Mid (FillSynEnvAp1 fill1) (FillSynEnvAp1 fill2) lt = <Ap< (FillSynEnvAna-<Low fill1 fill2 lt) refl
    FillSynEnvCon-<Mid (FillSynEnvAp2 fill1) (FillSynEnvAp2 fill2) lt = <Ap=< (FillSynEnvAna-<Low fill1 fill2 lt)
    FillSynEnvCon-<Mid (FillSynEnvPair1 fill1) (FillSynEnvPair1 fill2) lt = <Pair< (FillSynEnvAna-<Low fill1 fill2 lt) refl
    FillSynEnvCon-<Mid (FillSynEnvPair2 fill1) (FillSynEnvPair2 fill2) lt = <Pair=< (FillSynEnvAna-<Low fill1 fill2 lt)
    FillSynEnvCon-<Mid (FillSynEnvTypFun fill1) (FillSynEnvTypFun fill2) lt = <TypFun (FillSynEnvAna-<Low fill1 fill2 lt)
    FillSynEnvCon-<Mid (FillSynEnvTypAp fill1) (FillSynEnvTypAp fill2) lt = <TypAp (FillSynEnvAna-<Low fill1 fill2 lt)

    FillSynEnvAna-<Low : ∀ {ε e e' e-in e-in' s} ->
      ε S⟦ e-in' ⟧A≡ e' ->
      ε S⟦ e-in ⟧A≡ e ->
      <Up s e-in' e-in ->
      <Low (SkelFill s (skel-ul ε)) e' e
    FillSynEnvAna-<Low (FillSynEnvAnaRec fill1) (FillSynEnvAnaRec fill2) lt = <Lower= =★-refl (FillSynEnvSyn-<Up fill1 fill2 lt)
    
  FillAnaEnvAna-<AnaExp : ∀ {ε e e' e-in e-in'} ->
    ε A⟦ e-in' ⟧A≡ e' ->
    ε A⟦ e-in ⟧A≡ e ->
    <AnaExp e-in' e-in ->
    <AnaExp e' e
  FillAnaEnvAna-<AnaExp {ε} {e} {e'} fill1 fill2 (<AnaExp< lt) = <AnaExp< lt'
    where 
    lt' : surface-dirties-low e' < surface-dirties-low e
    lt' 
      rewrite FillAnaEnvAna-surface fill1 
      rewrite FillAnaEnvAna-surface fill2 
      = +-monoʳ-< (surface-dirties-ll ε) lt
  FillAnaEnvAna-<AnaExp {ε} {e} {e'} fill1 fill2 (<AnaExp= eq lt) = <AnaExp= eq' fill'
    where 
    eq' : surface-dirties-low e' ≡ surface-dirties-low e
    eq' 
      rewrite FillAnaEnvAna-surface fill1 
      rewrite FillAnaEnvAna-surface fill2 
      rewrite eq
      = refl
    fill' : <Low (SkelLow e') e' e
    fill' rewrite sym (skel-ll-comm fill1) = FillAnaEnvAna-<Low fill1 fill2 lt 

  FillSynEnvAna-<AnaExp : ∀ {ε e e' e-in e-in'} ->
    ε S⟦ e-in' ⟧A≡ e' ->
    ε S⟦ e-in ⟧A≡ e ->
    <SynExp e-in' e-in ->
    <AnaExp e' e
  FillSynEnvAna-<AnaExp {ε} {e} {e'} fill1 fill2 (<SynExp< lt) = <AnaExp< lt'
    where 
    lt' : surface-dirties-low e' < surface-dirties-low e
    lt' 
      rewrite FillSynEnvAna-surface fill1 
      rewrite FillSynEnvAna-surface fill2 
      = +-monoʳ-< (surface-dirties-ul ε) lt
  FillSynEnvAna-<AnaExp {ε} {e} {e'} fill1 fill2 (<SynExp= eq lt) = <AnaExp= eq' fill'
    where 
    eq' : surface-dirties-low e' ≡ surface-dirties-low e
    eq' 
      rewrite FillSynEnvAna-surface fill1 
      rewrite FillSynEnvAna-surface fill2 
      rewrite eq
      = refl
    fill' : <Low (SkelLow e') e' e 
    fill' rewrite sym (skel-ul-comm fill1) = FillSynEnvAna-<Low fill1 fill2 lt 
  
  StepDecreaseLow : ∀ {e e'} ->
    e A↦ e' -> 
    <AnaExp e' e
  StepDecreaseLow (StepLow fill1 step fill2) = FillAnaEnvAna-<AnaExp fill2 fill1 (StepDecreaseL step)
  StepDecreaseLow (StepUp fill1 step fill2) = FillSynEnvAna-<AnaExp fill2 fill1 (StepDecreaseU step)

  StepDecrease : ∀ {p p'} ->
    p' ↤P p -> 
    <Program p' p 
  StepDecrease TopStep = <Program= refl (<Lower= =★-refl (<Upper= <★C)) 
  StepDecrease {p} {p'} (InsideStep step) with StepDecreaseLow step
  ... | <AnaExp< lt = <Program< lt
  ... | <AnaExp= eq lt = <Program= eq lt
  
  mutual 

    translate-acc-up-old' : ∀{e t} ->
      (s : Skeleton) ->
      Acc (<Mid s) e ->
      ∀ {e'} ->
      (<Up s e' (e ⇒ (t , •))) -> 
      (Acc (<Up s) e')
    translate-acc-up-old' s (acc ac) (<Upper x) = translate-acc-up s (ac x)
    
    translate-acc-up-old : ∀{e t} ->
      (s : Skeleton) ->
      Acc (<Mid s) e ->
      Acc (<Up s) (e ⇒ (t , •))
    translate-acc-up-old s ac = acc (translate-acc-up-old' s ac)

    translate-acc-up' : ∀{e syn} ->
      (s : Skeleton) ->
      Acc (<Mid s) e ->
      ∀ {e'} ->
      (<Up s e' (e ⇒ syn)) -> 
      (Acc (<Up s) e') 
    translate-acc-up' s ac (<Upper= <★C) = translate-acc-up-old s ac
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
      (<Low s e' (e [ m ]⇐ (t , •))) -> 
      (Acc (<Low s) e') 
    translate-acc-low-old' s (acc ac) (<Lower= =★• lt) = translate-acc-low-old s (ac lt)

    translate-acc-low-old : ∀{e m t} ->
      (s : Skeleton) ->
      Acc (<Up s) e ->
      Acc (<Low s) (e [ m ]⇐ (t , •))
    translate-acc-low-old s ac = acc (translate-acc-low-old' s ac)

  mutual

    translate-acc-low'' : ∀{e m ana} ->
      (s : Skeleton) ->
      WellFounded (<Up s) ->
      (Acc (<Up s) e) -> 
      ∀ {e'} ->
      (<Low s e' (e [ m ]⇐ ana)) -> 
      (Acc (<Low s) e') 
    translate-acc-low'' s wf ac (<Lower <★C eq) = translate-acc-low-old s (wf _)
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

    translate-acc-proj' : ∀ {a1 a2 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      ∀ {e'} ->
      (<Mid (S1 s) e' (EProj a1 e a2)) -> 
      (Acc (<Mid (S1 s)) e') 
    translate-acc-proj' s (acc ac) (<Proj x) = translate-acc-proj s (ac x)
     
    translate-acc-proj : ∀ {a1 a2 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      Acc (<Mid (S1 s)) (EProj a1 e a2)
    translate-acc-proj s ac = acc (translate-acc-proj' s ac)

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
    translate-acc-ap'' s1 s2 wf1 wf2 (acc ac1) ac2 (<Ap< lt eq) = translate-acc-ap' s1 s2 wf1 wf2 (ac1 lt) (wf2 _)
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

    translate-acc-pair'' : ∀ {e1 e2 a} ->
      (s1 s2 : Skeleton) ->
      WellFounded (<Low s1) ->
      WellFounded (<Low s2) ->
      Acc (<Low s1) e1 ->
      Acc (<Low s2) e2 ->
      ∀ {e'} ->
      (<Mid (S2 s1 s2) e' (EPair e1 e2 a)) -> 
      (Acc (<Mid (S2 s1 s2)) e') 
    translate-acc-pair'' s1 s2 wf1 wf2 (acc ac1) ac2 (<Pair< lt eq) = translate-acc-pair' s1 s2 wf1 wf2 (ac1 lt) (wf2 _)
    translate-acc-pair'' s1 s2 wf1 wf2 ac1 (acc ac2) (<Pair=< lt) = translate-acc-pair' s1 s2 wf1 wf2 ac1 (ac2 lt)

    translate-acc-pair' : ∀ {e1 e2 a} ->
      (s1 s2 : Skeleton) ->
      WellFounded (<Low s1) ->
      WellFounded (<Low s2) ->
      Acc (<Low s1) e1 ->
      Acc (<Low s2) e2 ->
      Acc (<Mid (S2 s1 s2)) (EPair e1 e2 a)
    translate-acc-pair' s1 s2 wf1 wf2 ac1 ac2 = acc (translate-acc-pair'' s1 s2 wf1 wf2 ac1 ac2)

    translate-acc-pair : ∀ {e1 e2 a} ->
      (s1 s2 : Skeleton) ->
      WellFounded (<Low s1) ->
      WellFounded (<Low s2) ->
      Acc (<Mid (S2 s1 s2)) (EPair e1 e2 a)
    translate-acc-pair s1 s2 wf1 wf2 = translate-acc-pair' s1 s2 wf1 wf2 (wf1 _) (wf2 _) 

  mutual 

    translate-acc-typfun' : ∀ {a1 a2 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      ∀ {e'} ->
      (<Mid (S1 s) e' (ETypFun a1 a2 e)) -> 
      (Acc (<Mid (S1 s)) e') 
    translate-acc-typfun' s (acc ac) (<TypFun x) = translate-acc-typfun s (ac x)
     
    translate-acc-typfun : ∀ {a1 a2 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      Acc (<Mid (S1 s)) (ETypFun a1 a2 e)
    translate-acc-typfun s ac = acc (translate-acc-typfun' s ac)

  mutual 

    translate-acc-typap' : ∀ {a1 a2 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      ∀ {e'} ->
      (<Mid (S1 s) e' (ETypAp e a1 a2)) -> 
      (Acc (<Mid (S1 s)) e') 
    translate-acc-typap' s (acc ac) (<TypAp x) = translate-acc-typap s (ac x)
     
    translate-acc-typap : ∀ {a1 a2 e} ->
      (s : Skeleton) ->
      Acc (<Low s) e ->
      Acc (<Mid (S1 s)) (ETypAp e a1 a2)
    translate-acc-typap s ac = acc (translate-acc-typap' s ac)

  mutual 
    
    <Up-wf-old' : 
      (s : Skeleton) ->
      (e : ConExp) -> 
      {t : Data} -> 
      ∀ {e'} ->
      (<Up s e' (e ⇒ (t , •))) -> 
      (Acc (<Up s) e') 
    <Up-wf-old' s e (<Upper lt) = translate-acc-up s (<Mid-wf' s _ lt)

    <Up-wf-old : 
      (s : Skeleton) ->
      (e : ConExp) -> 
      {t : Data} -> 
      (Acc (<Up s) (e ⇒ (t , •))) 
    <Up-wf-old s e = acc (<Up-wf-old' s e)

    <Up-wf' : 
      (s : Skeleton) ->
      (e : SynExp) -> 
      ∀ {e'} ->
      (<Up s e' e) -> 
      (Acc (<Up s) e') 
    <Up-wf' s (e ⇒ _) (<Upper= <★C) = <Up-wf-old s e
    <Up-wf' s e (<Upper lt) = translate-acc-up s (<Mid-wf s _)
    
    <Up-wf : (s : Skeleton) -> WellFounded (<Up s)
    <Up-wf s e = acc (<Up-wf' s e)

    <Mid-wf' : 
      (s : Skeleton) ->
      (e : ConExp) -> 
      ∀ {e'} ->
      (<Mid s e' e) -> 
      (Acc (<Mid s) e') 
    <Mid-wf' s EConst ()
    <Mid-wf' s EHole ()
    <Mid-wf' s (EVar _ _) ()
    <Mid-wf' (S1 s) (EAsc _ e) (<Asc lt) = translate-acc-asc s (<Low-wf' s e lt)
    <Mid-wf' (S1 s) (EFun _ _ _ _ e) (<Fun lt) = translate-acc-fun s (<Low-wf' s e lt)
    <Mid-wf' (S1 s) (EProj _ e _) (<Proj lt) = translate-acc-proj s (<Low-wf' s e lt)
    <Mid-wf' (S2 s1 s2) (EAp e1 _ e2) (<Ap< {e1 = e3} {e4} lt eq) with <Low-wf s2
    ... | weird = translate-acc-ap s1 s2 (<Low-wf s1) weird
    <Mid-wf' (S2 s1 s2) (EAp e1 _ e2) (<Ap=< lt) = translate-acc-ap s1 s2 (<Low-wf s1) (<Low-wf s2)
    <Mid-wf' (S2 s1 s2) (EPair e1 e2 _) (<Pair< {e1 = e3} {e4} lt eq) with <Low-wf s2
    ... | weird = translate-acc-pair s1 s2 (<Low-wf s1) weird
    <Mid-wf' (S2 s1 s2) (EPair e1 e2 _) (<Pair=< lt) = translate-acc-pair s1 s2 (<Low-wf s1) (<Low-wf s2)
    <Mid-wf' (S1 s) (ETypFun _ _ e) (<TypFun lt) = translate-acc-typfun s (<Low-wf' s e lt)
    <Mid-wf' (S1 s) (ETypAp e _ _) (<TypAp lt) = translate-acc-typap s (<Low-wf' s e lt)

    <Mid-wf : (s : Skeleton) -> WellFounded (<Mid s)
    <Mid-wf s e = acc (<Mid-wf' s e)

    <Low-wf' : 
      (s : Skeleton) ->
      (e : AnaExp) -> 
      ∀ {e'} ->
      (<Low s e' e) -> 
      (Acc (<Low s) e') 
    <Low-wf' s e {x [ x₁ ]⇐ x₂} lt = translate-acc-low s (<Up-wf s)

    <Low-wf : (s : Skeleton) -> WellFounded (<Low s)
    <Low-wf s e = acc (<Low-wf' s e)

  <Program-wf'' : 
    (p : Program) -> 
    (n : ℕ) -> 
    (n ≡ surface-dirties-low (AnaExpOfProgram p)) ->
    Acc (_<_) n ->
    (s : Skeleton) ->
    (s ≡ SkelProgram p) ->
    Acc (<Low s) (AnaExpOfProgram p) ->
    ∀ {p'} ->
    (<Program p' p) -> 
    (Acc <Program p') 
  <Program-wf'' p n eq1 (acc rs) s eq2 ac {p'} (<Program< lt) = acc (<Program-wf'' p' _ refl (rs lt') _ refl (<Low-wf _ _))
    where 
    lt' : surface-dirties-low (AnaExpOfProgram p') < n
    lt' rewrite eq1 = lt
  <Program-wf'' p n eq1 ac1 s eq2 (acc rs) {p'} (<Program= eq3 lt) = acc (<Program-wf'' p' n eq1' ac1 s eq2' (rs lt'))
    where 
    lt' : <Low s (AnaExpOfProgram p') (AnaExpOfProgram p)
    lt' rewrite eq2 rewrite sym (<Low-skel lt) = lt
    eq1' : n ≡ surface-dirties-low (AnaExpOfProgram p') 
    eq1' rewrite eq1 rewrite eq3 = refl
    eq2' : s ≡ SkelLow (AnaExpOfProgram p') 
    eq2' rewrite eq2 = sym (<Low-skel lt)

  <Program-wf : WellFounded <Program 
  <Program-wf p = acc (<Program-wf'' p _ refl (<-wellFounded _) _ refl (<Low-wf _ _))

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