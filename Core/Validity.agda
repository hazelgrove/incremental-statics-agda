
open import Data.Product 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.WellTyped
open import Core.Settled
open import Core.Lemmas

module Core.Validity where

  data CtxOld : Ctx -> Set where 
    EmptyOld : CtxOld ∅
    ConsOld : ∀ {x t Γ} -> 
      CtxOld Γ -> 
      CtxOld (x ∶ (t , Old) ∷ Γ)
  
  ConsOld? : ∀ {x t Γ} -> 
    CtxOld Γ -> 
    CtxOld (x ∶ (t , Old) ∷? Γ)
  ConsOld? {BHole} ctx-old = ctx-old
  ConsOld? {BVar x} ctx-old = ConsOld ctx-old

  erase-∷? : ∀{x t n Γ} ->
    Γ◇ (x ∶ t , n ∷? Γ) ≡ x ∶ t ∷? (Γ◇ Γ)
  erase-∷? {BHole} = refl
  erase-∷? {BVar x} = refl

  ∈-of-∈N : ∀ {x t n m Γ} ->
    x , (t , n) ∈N Γ , m -> 
    x , t ∈ (Γ◇ Γ) , m
  ∈-of-∈N InCtxEmpty = InCtxEmpty
  ∈-of-∈N InCtxFound = InCtxFound
  ∈-of-∈N (InCtxSkip neq in-ctx) = InCtxSkip neq (∈-of-∈N in-ctx)

  all-old-lookup : ∀ {x nt nm Γ} ->
    x , nt ∈N Γ , nm ->
    CtxOld Γ ->
    ∃[ t ] nt ≡ (t , Old)
  all-old-lookup InCtxEmpty ctx-old = THole , refl
  all-old-lookup InCtxFound (ConsOld ctx-old) = _ , refl
  all-old-lookup (InCtxSkip neq in-ctx) (ConsOld ctx-old) = all-old-lookup in-ctx ctx-old

  barren-subsumable : ∀ {e} ->
    SubsumableMid e ->
    BareSubsumable (M◇ e)
  barren-subsumable SubsumableConst = BareSubsumableConst
  barren-subsumable SubsumableHole = BareSubsumableHole
  barren-subsumable SubsumableAp = BareSubsumableAp
  barren-subsumable SubsumableVar = BareSubsumableVar
  barren-subsumable SubsumableAsc = BareSubsumableAsc

  ana-edge-wt : ∀ {Γ e m t} ->
    Γ L⊢ ((e ⇒ (■ t , Old)) [ m ]⇐ (□ , Old)) -> 
    m ≡ ✔
  ana-edge-wt (WTUp _ (~N-pair ~DVoidR) ▶Old _) = refl
  ana-edge-wt (WTFun _ _ _ _ _ _ (~N-pair ~DVoidR) ▶Old _) = refl

  data ValidityUp : BareCtx -> BareExp -> ExpUp -> Set where 
    ValidityUpSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , Old)) ⇒ t -> 
      ValidityUp Γ b (e ⇒ (■ t , Old))

  data ValidityLow : BareCtx -> BareExp -> ExpLow -> Set where 
    ValidityLowSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , Old)) ⇒ t -> 
      ValidityLow Γ b ((e ⇒ (■ t , Old)) [ ✔ ]⇐ (□ , Old))
    ValidityLowAna : ∀ {Γ b e t m} ->
      Γ ⊢ b ~> (e [ m ]⇐ (■ t , Old)) ⇐ t -> 
      ValidityLow Γ b (e [ m ]⇐ (■ t , Old))

  mutual 
      
    validity-up : ∀ {Γ e} ->
      Γ U⊢ e ->
      e U̸↦ ->
      CtxOld Γ -> 
      ValidityUp (Γ◇ Γ) (U◇ e) e
    validity-up (WTConst (▷Pair ▶Old)) (SettledUp SettledConst) ctx-old = ValidityUpSyn MarkConst
    validity-up (WTHole (▷Pair ▶Old)) (SettledUp SettledHole) ctx-old = ValidityUpSyn MarkHole
    validity-up (WTAp (NTArrowC marrow) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old syn ana) (SettledUp (SettledAp (SettledLow settled1) (SettledLow settled2))) ctx-old with validity-low syn (SettledLow settled1) ctx-old | validity-low ana (SettledLow settled2) ctx-old
    ... | ValidityLowSyn syn' | ValidityLowAna ana' with marrow
    ... | DTArrowSome marrow = ValidityUpSyn (MarkAp syn' marrow ana')
    validity-up (WTVar in-ctx consist) (SettledUp SettledVar) ctx-old with all-old-lookup in-ctx ctx-old | consist
    ... | _ , refl | ▷Pair ▶Old = ValidityUpSyn (MarkVar (∈-of-∈N in-ctx))
    validity-up (WTAsc (▷Pair ▶Old) (▷Pair ▶Old) ana) (SettledUp (SettledAsc x₃)) ctx-old with validity-low ana x₃ ctx-old 
    ... | ValidityLowAna ana' = ValidityUpSyn (MarkAsc ana') 

    validity-low : ∀ {Γ e} ->
      Γ L⊢ e ->
      e L̸↦ ->
      CtxOld Γ -> 
      ValidityLow (Γ◇ Γ) (L◇ e) e
    validity-low (WTUp {ana-all = □ , n} x consist m-consist x₃) (SettledLow settled) ctx-old with validity-up x₃ settled ctx-old 
    ... | ValidityUpSyn syn with consist | m-consist
    ... | ~N-pair ~DVoidR | ▶Old = ValidityLowSyn syn
    validity-low (WTUp {ana-all = ■ t , n} subsumable consist m-consist syn) (SettledLow settled) ctx-old with validity-up syn settled ctx-old 
    ... | ValidityUpSyn syn' with consist | m-consist
    ... | (~N-pair (~DSome consist)) | ▶Old = ValidityLowAna (MarkSubsume syn' (barren-subsumable subsumable) consist)
    validity-low {Γ} (WTFun {x = x} {ana-all = □ , .Old} (NTArrowC DTArrowNone) consist (▷Pair ▶Old) ▶Old c3 c4 (~N-pair consist') c5 ana) (SettledLow (SettledUp (SettledFun {t = t} settled))) ctx-old with validity-low ana settled (ConsOld? ctx-old)
    ... | ValidityLowSyn syn rewrite erase-∷? {x} {t} {Old} {Γ}  with consist | c3 | c4 | c5
    ... | ■~N-pair (~N-pair ~DVoidR) | ▶Old | ▷Pair ▶Old | ▶Old with ~DVoid-right consist' 
    ... | refl = ValidityLowSyn (MarkSynFun syn)
    validity-low {Γ} (WTFun {x = x} {ana-all = ■ t , .Old} (NTArrowC (DTArrowSome marrow)) (■~N-pair (~N-pair (~DSome consist))) (▷Pair ▶Old) ▶Old ▶Old (▷Pair ▶Old) consist' c5 ana) (SettledLow (SettledUp (SettledFun {t = t'} settled))) ctx-old 
      with validity-low ana settled (ConsOld? ctx-old)
    ... | ValidityLowAna ana' rewrite erase-∷? {x} {t'} {Old} {Γ} with consist' | c5 
    ... | ~N-pair ~DVoidL | ▶Old = ValidityLowAna (MarkAnaFun marrow ana' consist)

  validity : ∀ {p} ->
    P⊢ p ->
    p P̸↦ ->
    ((P◇ p) ~> p)
  validity {p = Root e n} (WTProgram ana) (SettledProgram settled) with validity-low ana settled EmptyOld 
  ... | ValidityLowSyn syn = MarkProgram syn
 