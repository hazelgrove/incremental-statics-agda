
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
    TCons• : ∀ {x Γ} -> 
      Ctx• Γ -> 
      Ctx• (x T∷ Γ)
  
  Cons•? : ∀ {x t Γ} -> 
    Ctx• Γ -> 
    Ctx• (x ∶ (t , •) ∷? Γ)
  Cons•? {BHole} ctx-old = ctx-old
  Cons•? {BVar x} ctx-old = Cons• ctx-old
  
  TCons•? : ∀ {x Γ} -> 
    Ctx• Γ -> 
    Ctx• (x T∷? Γ)
  TCons•? {BHole} ctx-old = ctx-old
  TCons•? {BVar x} ctx-old = TCons• ctx-old

  ◇T∷? : ∀{x Γ} ->
    Γ◇ (x T∷? Γ) ≡ x T∷? (Γ◇ Γ)
  ◇T∷? {BHole} = refl
  ◇T∷? {BVar x} = refl

  ◇∷? : ∀{x t n Γ} ->
    Γ◇ (x ∶ t , n ∷? Γ) ≡ x ∶ t ∷? (Γ◇ Γ)
  ◇∷? {BHole} = refl
  ◇∷? {BVar x} = refl

  ◇T∈ : ∀ {x m Γ} ->
    x T∈ Γ , m -> 
    x T∈ (Γ◇ Γ) , m
  ◇T∈ InCtxEmpty = InCtxEmpty
  ◇T∈ InCtxFound = InCtxFound
  ◇T∈ (InCtxSkip in-ctx) = InCtxSkip (◇T∈ in-ctx)
  ◇T∈ (InCtxTSkip x in-ctx) = InCtxTSkip x (◇T∈ in-ctx)

  ◇∈ : ∀ {x t n m Γ} ->
    x , (t , n) ∈ Γ , m -> 
    x , t ∈ (Γ◇ Γ) , m
  ◇∈ InCtxEmpty = InCtxEmpty
  ◇∈ InCtxFound = InCtxFound
  ◇∈ (InCtxSkip neq in-ctx) = InCtxSkip neq (◇∈ in-ctx)
  ◇∈ (InCtxTSkip in-ctx) = InCtxTSkip (◇∈ in-ctx)

  all-old-lookup : ∀ {x nt nm Γ} ->
    x , nt ∈ Γ , nm ->
    Ctx• Γ ->
    ∃[ t ] nt ≡ (t , •)
  all-old-lookup InCtxEmpty ctx-old = THole , refl
  all-old-lookup InCtxFound (Cons• ctx-old) = _ , refl
  all-old-lookup (InCtxSkip neq in-ctx) (Cons• ctx-old) = all-old-lookup in-ctx ctx-old
  all-old-lookup (InCtxTSkip in-ctx) (TCons• ctx-old) = all-old-lookup in-ctx ctx-old

  barren-subsumable : ∀ {e} ->
    SubsumableMid e ->
    BareSubsumable (C◇ e)
  barren-subsumable SubsumableConst = BareSubsumableConst
  barren-subsumable SubsumableHole = BareSubsumableHole
  barren-subsumable SubsumableAp = BareSubsumableAp
  barren-subsumable SubsumableVar = BareSubsumableVar
  barren-subsumable SubsumableAsc = BareSubsumableAsc
  barren-subsumable SubsumableProj = BareSubsumableProj
  barren-subsumable SubsumableTypAp = BareSubsumableTypAp

  -- ana-edge-wt : ∀ {Γ e m t} ->
  --   Γ A⊢ ((e ⇒ (■ t , •)) [ m ]⇐ (□ , •)) -> 
  --   m ≡ ✔
  -- ana-edge-wt (WFSubsume _ (~N-pair ~DVoidR) ▶• _) = refl
  -- ana-edge-wt (WFFun _ _ _ _ _ _ _ (~N-pair ~DVoidR) ▶• _) = refl
  -- ana-edge-wt (WFPair _ _ _ _ _ (~N-pair ~DVoidR) ▶• _ _) = refl
  -- ana-edge-wt wf = ?

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


  validity-typ : ∀ {Γ t} ->
    Γ T⊢ t ->
    Γ◇ Γ ⊢ T◇ t T~> t
  validity-typ WFBase = MarkBase
  validity-typ WFHole = MarkHole
  validity-typ (WFArrow wf1 wf2) = MarkArrow (validity-typ wf1) (validity-typ wf2)
  validity-typ (WFProd wf1 wf2) = MarkProd (validity-typ wf1) (validity-typ wf2)
  validity-typ (WFTVar in-ctx) = MarkTVar (◇T∈ in-ctx)
  validity-typ {Γ = Γ} (WFForall {x = x} wf) with validity-typ wf 
  ... | valid rewrite (◇T∷? {x} {Γ}) = MarkForall valid

  mutual 
      
    quiescent-validity-up : ∀ {Γ e} ->
      Γ S⊢ e ->
      e S̸↦ ->
      Ctx• Γ -> 
      QuiescentValidityUp (Γ◇ Γ) (S◇ e) e
    quiescent-validity-up (WFConst (▷Pair ▶•)) (QuiescentUp QuiescentConst) ctx-old = QuiescentValidityUpSyn MarkConst
    quiescent-validity-up (WFHole (▷Pair ▶•)) (QuiescentUp QuiescentHole) ctx-old = QuiescentValidityUpSyn MarkHole
    quiescent-validity-up (WFAp (NTArrowC marrow) (▷Pair ▶•) (▷Pair ▶•) ▶• syn ana) (QuiescentUp (QuiescentAp (QuiescentLow settled1) (QuiescentLow settled2))) ctx-old with quiescent-validity-low syn (QuiescentLow settled1) ctx-old | quiescent-validity-low ana (QuiescentLow settled2) ctx-old
    ... | QuiescentValidityLowSyn syn' | QuiescentValidityLowAna ana' with marrow
    ... | DTArrowSome marrow = QuiescentValidityUpSyn (MarkAp syn' marrow ana')
    quiescent-validity-up (WFVar in-ctx consist) (QuiescentUp QuiescentVar) ctx-old with all-old-lookup in-ctx ctx-old | consist
    ... | _ , refl | ▷Pair ▶• = QuiescentValidityUpSyn (MarkVar (◇∈ in-ctx))
    quiescent-validity-up (WFAsc wf (▷Pair ▶•) (▷Pair ▶•) ana) (QuiescentUp (QuiescentAsc x₃)) ctx-old with quiescent-validity-low ana x₃ ctx-old 
    ... | QuiescentValidityLowAna ana' = QuiescentValidityUpSyn (MarkAsc (validity-typ wf) ana') 
    quiescent-validity-up (WFProj (NTProjC mprod) (▷Pair c1) c2 syn) (QuiescentUp (QuiescentProj (QuiescentLow settled))) ctx-old with quiescent-validity-low syn (QuiescentLow settled) ctx-old 
    ... | QuiescentValidityLowSyn syn' with mprod | c1 | c2 
    ... | DTProjSome x | ▶• | ▶• = QuiescentValidityUpSyn (MarkProj syn' x)
    quiescent-validity-up (WFTypAp typ mforall c1 sub c2 syn) (QuiescentUp (QuiescentTypAp q)) ctx-old with quiescent-validity-low syn q ctx-old 
    ... | QuiescentValidityLowSyn syn' with mforall | sub | c1 | c2 
    ... | NTForallC (DTForallSome mforall) | NSub-pair (NSubSome sub) | ▶• | ▷Pair ▶• = QuiescentValidityUpSyn (MarkTypAp syn' mforall (validity-typ typ) sub)

    quiescent-validity-low : ∀ {Γ e} ->
      Γ A⊢ e ->
      e A̸↦ ->
      Ctx• Γ -> 
      QuiescentValidityLow (Γ◇ Γ) (A◇ e) e
    quiescent-validity-low (WFSubsume {ana-all = □ , n} x consist m-consist x₃) (QuiescentLow settled) ctx-old with quiescent-validity-up x₃ settled ctx-old 
    ... | QuiescentValidityUpSyn syn with consist | m-consist
    ... | ~N-pair ~DVoidR | ▶• = QuiescentValidityLowSyn syn
    quiescent-validity-low (WFSubsume {ana-all = ■ t , n} subsumable consist m-consist syn) (QuiescentLow settled) ctx-old with quiescent-validity-up syn settled ctx-old 
    ... | QuiescentValidityUpSyn syn' with consist | m-consist
    ... | (~N-pair (~DSome consist)) | ▶• = QuiescentValidityLowAna (MarkSubsume syn' (barren-subsumable subsumable) consist)
    quiescent-validity-low {Γ} (WFFun {x = x} {ana-all = □ , .•} wf (NTArrowC DTArrowNone) consist (▷Pair ▶•) ▶• c3 c4 (~N-pair consist') c5 ana) (QuiescentLow (QuiescentUp (QuiescentFun {t = t} settled))) ctx-old with quiescent-validity-low ana settled (Cons•? ctx-old)
    ... | QuiescentValidityLowSyn syn rewrite ◇∷? {x} {t} {•} {Γ}  with consist | c3 | c4 | c5
    ... | ■~N-pair (~N-pair ~DVoidR) | ▶• | ▷Pair ▶• | ▶• with ~DVoid-right consist' 
    ... | refl = QuiescentValidityLowSyn (MarkSynFun (validity-typ wf) syn)
    quiescent-validity-low {Γ} (WFFun {x = x} {ana-all = ■ t , .•} wf (NTArrowC (DTArrowSome marrow)) (■~N-pair (~N-pair (~DSome consist))) (▷Pair ▶•) ▶• ▶• (▷Pair ▶•) consist' c5 ana) (QuiescentLow (QuiescentUp (QuiescentFun {t = t'} settled))) ctx-old 
      with quiescent-validity-low ana settled (Cons•? ctx-old)
    ... | QuiescentValidityLowAna ana' rewrite ◇∷? {x} {t'} {•} {Γ} with consist' | c5 
    ... | ~N-pair ~DVoidL | ▶• = QuiescentValidityLowAna (MarkAnaFun (validity-typ wf) marrow ana' consist)
    quiescent-validity-low {Γ} (WFPair {ana-all = □ , .•} (NTProdC DTProdNone) (▷Pair ▶•) (▷Pair ▶•) ▶• x₄ (~N-pair x) ▶• syn1 syn2) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) ctx-old 
      with quiescent-validity-low syn1 settled1 ctx-old | quiescent-validity-low syn2 settled2 ctx-old
    ... | QuiescentValidityLowSyn x₁ | QuiescentValidityLowSyn x₂ with x | x₄ 
    ... | ~DVoidR | ▷Pair ▶• = QuiescentValidityLowSyn (MarkSynPair x₁ x₂)
    quiescent-validity-low {Γ} (WFPair {ana-all = ■ x₉ , .•} (NTProdC (DTProdSome mprod)) (▷Pair ▶•) (▷Pair ▶•) ▶• x₄ (~N-pair x) ▶• ana1 ana2) (QuiescentLow (QuiescentUp (QuiescentPair settled1 settled2))) ctx-old -- = {!   !}
      with quiescent-validity-low ana1 settled1 ctx-old | quiescent-validity-low ana2 settled2 ctx-old
    ... | QuiescentValidityLowAna x₁ | QuiescentValidityLowAna x₂ with x | x₄ 
    ... | ~DVoidL | ▷Pair ▶• = QuiescentValidityLowAna (MarkAnaPair mprod x₁ x₂) 
    quiescent-validity-low {Γ} (WFTypFun {x = x} {ana-all = □ , .•} (NTForallBindC mforall) (▷Pair ▶•) ▶• (▷Pair c1) (~N-pair con) ▶• ana) (QuiescentLow (QuiescentUp (QuiescentTypFun q))) ctx-old 
      with quiescent-validity-low ana q (TCons•? ctx-old) | mforall | c1 | con 
    ... | QuiescentValidityLowSyn syn' | DTForallBindNone | ▶• | ~DVoidR rewrite ◇T∷? {x} {Γ} = QuiescentValidityLowSyn (MarkSynTypFun syn')
    quiescent-validity-low {Γ} (WFTypFun {x = x} {ana-all =  ■ t , .•} (NTForallBindC mforall) (▷Pair ▶•) ▶• (▷Pair c1) (~N-pair con) ▶• ana) (QuiescentLow (QuiescentUp (QuiescentTypFun q))) ctx-old 
      with quiescent-validity-low ana q (TCons•? ctx-old) | mforall | c1 | con 
    ... | QuiescentValidityLowAna ana' | DTForallBindSome mforall | ▶• | ~DVoidL rewrite ◇T∷? {x} {Γ} = QuiescentValidityLowAna (MarkAnaTypFun mforall ana') 

  quiescent-validity : ∀ {p} ->
    P⊢ p ->
    p P̸↦ ->
    ((P◇ p) ~> p)
  quiescent-validity {p = Root e n} (WFProgram ana) (QuiescentProgram settled) with quiescent-validity-low ana settled Empty• 
  ... | QuiescentValidityLowSyn syn = MarkProgram syn
     