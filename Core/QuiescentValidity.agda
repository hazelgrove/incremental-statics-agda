
open import Data.Product 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Marking
open import Core.WellFormed
open import Core.Quiescent
open import Core.Lemmas

module Core.QuiescentValidity where

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

  data QuiescentValidityUp : BareCtx -> BareExp -> SynExp -> Set where 
    QuiescentValidityUpSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , •)) ⇒ t -> 
      QuiescentValidityUp Γ b (e ⇒ (■ t , •))

  data QuiescentValidityLow : BareCtx -> BareExp -> AnaExp -> Set where 
    QuiescentValidityLowSyn : ∀ {Γ b e t} ->
      Γ ⊢ b ~> (e ⇒ (■ t , •)) ⇒ t -> 
      QuiescentValidityLow Γ b ((e ⇒ (■ t , •)) [ ✔ ]⇐ (□ , •))
    QuiescentValidityLowAna : ∀ {Γ b e t m} ->
      Γ ⊢ b ~> (e [ m ]⇐ (■ t , •)) ⇐ t -> 
      QuiescentValidityLow Γ b (e [ m ]⇐ (■ t , •))

  mutual 
      
    quiescent-validity-up : ∀ {Γ e} ->
      Γ S⊢ e ->
      e U̸↦ ->
      Ctx• Γ -> 
      QuiescentValidityUp (Γ◇ Γ) (U◇ e) e
    quiescent-validity-up (WFConst (▷Pair ▶•)) (QuiescentUp QuiescentConst) ctx-old = QuiescentValidityUpSyn MarkConst
    quiescent-validity-up (WFHole (▷Pair ▶•)) (QuiescentUp QuiescentHole) ctx-old = QuiescentValidityUpSyn MarkHole
    quiescent-validity-up (WFAp (NTArrowC marrow) (▷Pair ▶•) (▷Pair ▶•) ▶• syn ana) (QuiescentUp (QuiescentAp (QuiescentLow settled1) (QuiescentLow settled2))) ctx-old with quiescent-validity-low syn (QuiescentLow settled1) ctx-old | quiescent-validity-low ana (QuiescentLow settled2) ctx-old
    ... | QuiescentValidityLowSyn syn' | QuiescentValidityLowAna ana' with marrow
    ... | DTArrowSome marrow = QuiescentValidityUpSyn (MarkAp syn' marrow ana')
    quiescent-validity-up (WFVar in-ctx consist) (QuiescentUp QuiescentVar) ctx-old with all-old-lookup in-ctx ctx-old | consist
    ... | _ , refl | ▷Pair ▶• = QuiescentValidityUpSyn (MarkVar (∈-of-∈N in-ctx))
    quiescent-validity-up (WFAsc (▷Pair ▶•) (▷Pair ▶•) ana) (QuiescentUp (QuiescentAsc x₃)) ctx-old with quiescent-validity-low ana x₃ ctx-old 
    ... | QuiescentValidityLowAna ana' = QuiescentValidityUpSyn (MarkAsc ana') 
    quiescent-validity-up (WFProj (NTProjC mprod) (▷Pair c1) c2 syn) (QuiescentUp (QuiescentProj (QuiescentLow settled))) ctx-old with quiescent-validity-low syn (QuiescentLow settled) ctx-old 
    ... | QuiescentValidityLowSyn syn' with mprod | c1 | c2 
    ... | DTProjSome x | ▶• | ▶• = QuiescentValidityUpSyn (MarkProj syn' x)

    quiescent-validity-low : ∀ {Γ e} ->
      Γ L⊢ e ->
      e L̸↦ ->
      Ctx• Γ -> 
      QuiescentValidityLow (Γ◇ Γ) (L◇ e) e
    quiescent-validity-low (WFSubsume {ana-all = □ , n} x consist m-consist x₃) (QuiescentLow settled) ctx-old with quiescent-validity-up x₃ settled ctx-old 
    ... | QuiescentValidityUpSyn syn with consist | m-consist
    ... | ~N-pair ~DVoidR | ▶• = QuiescentValidityLowSyn syn
    quiescent-validity-low (WFSubsume {ana-all = ■ t , n} subsumable consist m-consist syn) (QuiescentLow settled) ctx-old with quiescent-validity-up syn settled ctx-old 
    ... | QuiescentValidityUpSyn syn' with consist | m-consist
    ... | (~N-pair (~DSome consist)) | ▶• = QuiescentValidityLowAna (MarkSubsume syn' (barren-subsumable subsumable) consist)
    quiescent-validity-low {Γ} (WFFun {x = x} {ana-all = □ , .•} (NTArrowC DTArrowNone) consist (▷Pair ▶•) ▶• c3 c4 (~N-pair consist') c5 ana) (QuiescentLow (QuiescentUp (QuiescentFun {t = t} settled))) ctx-old with quiescent-validity-low ana settled (Cons•? ctx-old)
    ... | QuiescentValidityLowSyn syn rewrite erase-∷? {x} {t} {•} {Γ}  with consist | c3 | c4 | c5
    ... | ■~N-pair (~N-pair ~DVoidR) | ▶• | ▷Pair ▶• | ▶• with ~DVoid-right consist' 
    ... | refl = QuiescentValidityLowSyn (MarkSynFun syn)
    quiescent-validity-low {Γ} (WFFun {x = x} {ana-all = ■ t , .•} (NTArrowC (DTArrowSome marrow)) (■~N-pair (~N-pair (~DSome consist))) (▷Pair ▶•) ▶• ▶• (▷Pair ▶•) consist' c5 ana) (QuiescentLow (QuiescentUp (QuiescentFun {t = t'} settled))) ctx-old 
      with quiescent-validity-low ana settled (Cons•? ctx-old)
    ... | QuiescentValidityLowAna ana' rewrite erase-∷? {x} {t'} {•} {Γ} with consist' | c5 
    ... | ~N-pair ~DVoidL | ▶• = QuiescentValidityLowAna (MarkAnaFun marrow ana' consist)
    quiescent-validity-low {Γ} (WFPair {ana-all = □ , .•} (NTProdC DTProdNone) (▷Pair ▶•) (▷Pair ▶•) ▶• x₄ (~N-pair x) ▶• syn1 syn2) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) ctx-old 
      with quiescent-validity-low syn1 settled1 ctx-old | quiescent-validity-low syn2 settled2 ctx-old
    ... | QuiescentValidityLowSyn x₁ | QuiescentValidityLowSyn x₂ with x | x₄ 
    ... | ~DVoidR | ▷Pair ▶• = QuiescentValidityLowSyn (MarkSynPair x₁ x₂)
    quiescent-validity-low {Γ} (WFPair {ana-all = ■ x₉ , .•} (NTProdC (DTProdSome mprod)) (▷Pair ▶•) (▷Pair ▶•) ▶• x₄ (~N-pair x) ▶• ana1 ana2) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) ctx-old -- = {!   !}
      with quiescent-validity-low ana1 settled1 ctx-old | quiescent-validity-low ana2 settled2 ctx-old
    ... | QuiescentValidityLowAna x₁ | QuiescentValidityLowAna x₂ with x | x₄ 
    ... | ~DVoidL | ▷Pair ▶• = QuiescentValidityLowAna (MarkAnaPair mprod x₁ x₂) 

  quiescent-validity : ∀ {p} ->
    P⊢ p ->
    p P̸↦ ->
    ((P◇ p) ~> p)
  quiescent-validity {p = Root e n} (WFProgram ana) (QuiescentProgram settled) with quiescent-validity-low ana settled Empty• 
  ... | QuiescentValidityLowSyn syn = MarkProgram syn
 