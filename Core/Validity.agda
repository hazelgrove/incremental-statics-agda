
open import Data.Product 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.WellFormed
open import Core.Settled
open import Core.Lemmas

module Core.Validity where

  data Ctx• : Ctx -> Set where 
    Empty• : Ctx• ∅
    Cons• : ∀ {x t Γ} -> 
      Ctx• Γ -> 
      Ctx• (x ∶ (t , •) ∷ Γ)
  
  Cons•? : ∀ {x t Γ} -> 
    Ctx• Γ -> 
    Ctx• (x ∶ (t , •) ∷? Γ)
  Cons•? {BHole} ctx-old = ctx-old
  Cons•? {BVar x} ctx-old = Cons• ctx-old

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
    Ctx• Γ ->
    ∃[ t ] nt ≡ (t , •)
  all-old-lookup InCtxEmpty ctx-old = THole , refl
  all-old-lookup InCtxFound (Cons• ctx-old) = _ , refl
  all-old-lookup (InCtxSkip neq in-ctx) (Cons• ctx-old) = all-old-lookup in-ctx ctx-old

  barren-subsumable : ∀ {e} ->
    SubsumableMid e ->
    BareSubsumable (M◇ e)
  barren-subsumable SubsumableConst = BareSubsumableConst
  barren-subsumable SubsumableHole = BareSubsumableHole
  barren-subsumable SubsumableAp = BareSubsumableAp
  barren-subsumable SubsumableVar = BareSubsumableVar
  barren-subsumable SubsumableAsc = BareSubsumableAsc
  barren-subsumable SubsumableProj = BareSubsumableProj

  ana-edge-wt : ∀ {Γ e m t} ->
    Γ L⊢ ((e ⇒ (■ t , •)) [ m ]⇐ (□ , •)) -> 
    m ≡ ✔
  ana-edge-wt (WFSubsume _ (~N-pair ~DVoidR) ▶• _) = refl
  ana-edge-wt (WFFun _ _ _ _ _ _ (~N-pair ~DVoidR) ▶• _) = refl
  ana-edge-wt (WFPair _ _ _ _ _ (~N-pair ~DVoidR) ▶• _ _) = refl

  data ValidityUp : BareCtx -> BareExp -> ExpUp -> Set where 
    ValidityUpSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , •)) ⇒ t -> 
      ValidityUp Γ b (e ⇒ (■ t , •))

  data ValidityLow : BareCtx -> BareExp -> ExpLow -> Set where 
    ValidityLowSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , •)) ⇒ t -> 
      ValidityLow Γ b ((e ⇒ (■ t , •)) [ ✔ ]⇐ (□ , •))
    ValidityLowAna : ∀ {Γ b e t m} ->
      Γ ⊢ b ~> (e [ m ]⇐ (■ t , •)) ⇐ t -> 
      ValidityLow Γ b (e [ m ]⇐ (■ t , •))

  mutual 
      
    validity-up : ∀ {Γ e} ->
      Γ U⊢ e ->
      e U̸↦ ->
      Ctx• Γ -> 
      ValidityUp (Γ◇ Γ) (U◇ e) e
    validity-up (WFConst (▷Pair ▶•)) (SettledUp SettledConst) ctx-old = ValidityUpSyn MarkConst
    validity-up (WFHole (▷Pair ▶•)) (SettledUp SettledHole) ctx-old = ValidityUpSyn MarkHole
    validity-up (WFAp (NTArrowC marrow) (▷Pair ▶•) (▷Pair ▶•) ▶• syn ana) (SettledUp (SettledAp (SettledLow settled1) (SettledLow settled2))) ctx-old with validity-low syn (SettledLow settled1) ctx-old | validity-low ana (SettledLow settled2) ctx-old
    ... | ValidityLowSyn syn' | ValidityLowAna ana' with marrow
    ... | DTArrowSome marrow = ValidityUpSyn (MarkAp syn' marrow ana')
    validity-up (WFVar in-ctx consist) (SettledUp SettledVar) ctx-old with all-old-lookup in-ctx ctx-old | consist
    ... | _ , refl | ▷Pair ▶• = ValidityUpSyn (MarkVar (∈-of-∈N in-ctx))
    validity-up (WFAsc (▷Pair ▶•) (▷Pair ▶•) ana) (SettledUp (SettledAsc x₃)) ctx-old with validity-low ana x₃ ctx-old 
    ... | ValidityLowAna ana' = ValidityUpSyn (MarkAsc ana') 
    validity-up (WFProj (NTProjC mprod) (▷Pair c1) c2 syn) (SettledUp (SettledProj (SettledLow settled))) ctx-old with validity-low syn (SettledLow settled) ctx-old 
    ... | ValidityLowSyn syn' with mprod | c1 | c2 
    ... | DTProjSome x | ▶• | ▶• = ValidityUpSyn (MarkProj syn' x)

    validity-low : ∀ {Γ e} ->
      Γ L⊢ e ->
      e L̸↦ ->
      Ctx• Γ -> 
      ValidityLow (Γ◇ Γ) (L◇ e) e
    validity-low (WFSubsume {ana-all = □ , n} x consist m-consist x₃) (SettledLow settled) ctx-old with validity-up x₃ settled ctx-old 
    ... | ValidityUpSyn syn with consist | m-consist
    ... | ~N-pair ~DVoidR | ▶• = ValidityLowSyn syn
    validity-low (WFSubsume {ana-all = ■ t , n} subsumable consist m-consist syn) (SettledLow settled) ctx-old with validity-up syn settled ctx-old 
    ... | ValidityUpSyn syn' with consist | m-consist
    ... | (~N-pair (~DSome consist)) | ▶• = ValidityLowAna (MarkSubsume syn' (barren-subsumable subsumable) consist)
    validity-low {Γ} (WFFun {x = x} {ana-all = □ , .•} (NTArrowC DTArrowNone) consist (▷Pair ▶•) ▶• c3 c4 (~N-pair consist') c5 ana) (SettledLow (SettledUp (SettledFun {t = t} settled))) ctx-old with validity-low ana settled (Cons•? ctx-old)
    ... | ValidityLowSyn syn rewrite erase-∷? {x} {t} {•} {Γ}  with consist | c3 | c4 | c5
    ... | ■~N-pair (~N-pair ~DVoidR) | ▶• | ▷Pair ▶• | ▶• with ~DVoid-right consist' 
    ... | refl = ValidityLowSyn (MarkSynFun syn)
    validity-low {Γ} (WFFun {x = x} {ana-all = ■ t , .•} (NTArrowC (DTArrowSome marrow)) (■~N-pair (~N-pair (~DSome consist))) (▷Pair ▶•) ▶• ▶• (▷Pair ▶•) consist' c5 ana) (SettledLow (SettledUp (SettledFun {t = t'} settled))) ctx-old 
      with validity-low ana settled (Cons•? ctx-old)
    ... | ValidityLowAna ana' rewrite erase-∷? {x} {t'} {•} {Γ} with consist' | c5 
    ... | ~N-pair ~DVoidL | ▶• = ValidityLowAna (MarkAnaFun marrow ana' consist)
    validity-low {Γ} (WFPair {ana-all = □ , .•} (NTProdC DTProdNone) (▷Pair ▶•) (▷Pair ▶•) ▶• x₄ (~N-pair x) ▶• syn1 syn2) (SettledLow (SettledUp (SettledPair settled1 settled2))) ctx-old 
      with validity-low syn1 settled1 ctx-old | validity-low syn2 settled2 ctx-old
    ... | ValidityLowSyn x₁ | ValidityLowSyn x₂ with x | x₄ 
    ... | ~DVoidR | ▷Pair ▶• = ValidityLowSyn (MarkSynPair x₁ x₂)
    validity-low {Γ} (WFPair {ana-all = ■ x₉ , .•} (NTProdC (DTProdSome mprod)) (▷Pair ▶•) (▷Pair ▶•) ▶• x₄ (~N-pair x) ▶• ana1 ana2) (SettledLow (SettledUp (SettledPair settled1 settled2))) ctx-old -- = {!   !}
      with validity-low ana1 settled1 ctx-old | validity-low ana2 settled2 ctx-old
    ... | ValidityLowAna x₁ | ValidityLowAna x₂ with x | x₄ 
    ... | ~DVoidL | ▷Pair ▶• = ValidityLowAna (MarkAnaPair mprod x₁ x₂) 

  validity : ∀ {p} ->
    P⊢ p ->
    p P̸↦ ->
    ((P◇ p) ~> p)
  validity {p = Root e n} (WFProgram ana) (SettledProgram settled) with validity-low ana settled Empty• 
  ... | ValidityLowSyn syn = MarkProgram syn
 