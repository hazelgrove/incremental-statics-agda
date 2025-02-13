
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.Environment
open import Core.WellTyped
open import Core.MarkingUnicity

module Core.Lemmas where

  data =▷ {A : Set} : NEW A -> NEW A -> Set where 
    =▷New : ∀ {s t} -> 
      =▷ s (t , New)
    =▷Refl : ∀ {s} -> 
      =▷ s s

  data ◁▷ {A : Set} : NEW A -> NEW A -> Set where 
    ◁▷C : ∀ {t n n'} -> 
      ◁▷ (t , n) (t , n')

  max-new : (n : Newness) -> n ⊓ New ≡ New 
  max-new Old = refl
  max-new New = refl

  ~DVoid-right : ∀ {t m} ->
    t ~D □ , m ->
    m ≡ ✔
  ~DVoid-right ~DVoidL = refl
  ~DVoid-right ~DVoidR = refl

  ~D-unless : ∀ {t1 t2} ->
    DUnless t1 t2 ~D t2 , ✔
  ~D-unless {t2 = □} = ~DVoidR
  ~D-unless {t2 = ■ x} = ~DVoidL 

  new-through-~N-left : ∀ {d t m} ->
    d ~N (t , New) , m -> 
    ∃[ m' ] m ≡ (m' , New)
  new-through-~N-left (~N-pair {n1 = n1} consist) rewrite max-new n1 = _ , refl

  ▶Same : ∀ {n} ->
    {A : Set} ->
    {a : A} ->
    ▶ (a , n) a
  ▶Same {Old} = ▶Old
  ▶Same {New} = ▶New

  ▶New-max-r : ∀ {n} -> 
    {A : Set} -> 
    {a a' : A} ->
    ▶ (a , (n ⊓ New)) a'
  ▶New-max-r {n = n} rewrite max-new n = ▶New

  ▸TArrow-dec : 
    (t : Type) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸TArrow t-in , t-out , m
  ▸TArrow-dec TBase = THole , THole , ✖ , MArrowBase
  ▸TArrow-dec THole = THole , THole , ✔ , MArrowHole
  ▸TArrow-dec (TArrow t1 t2) = t1 , t2 , ✔ , MArrowArrow

  ▸DTArrow-dec : 
    (t : Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸DTArrow t-in , t-out , m
  ▸DTArrow-dec □ = □ , □ , ✔ , DTArrowNone
  ▸DTArrow-dec (■ t) with ▸TArrow-dec t 
  ... | t1 , t2 , m , match = ■ t1 , ■ t2 , m , DTArrowSome match

  ▸NTArrow-dec : 
    (d : NewData) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] d ▸NTArrow t-in , t-out , m
  ▸NTArrow-dec (d , n) with ▸DTArrow-dec d 
  ... | t1 , t2 , m , match = (t1 , n) , (t2 , n) , (m , n) , NTArrowC match

  ~-dec : 
    (syn ana : Type) -> 
    ∃[ m ] syn ~ ana , m 
  ~-dec TBase TBase = ✔ , ConsistBase
  ~-dec TBase THole = ✔ , ConsistHoleR
  ~-dec TBase (TArrow _ _) = ✖ , InconsistBaseArr
  ~-dec THole TBase = ✔ , ConsistHoleL
  ~-dec THole THole = ✔ , ConsistHoleR
  ~-dec THole (TArrow _ _) = ✔ , ConsistHoleL
  ~-dec (TArrow _ _) TBase = ✖ , InconsistArrBase
  ~-dec (TArrow _ _) THole = ✔ , ConsistHoleR
  ~-dec (TArrow syn1 syn2) (TArrow ana1 ana2) with ~-dec syn1 ana1 | ~-dec syn2 ana2 
  ... | m1 , consist1 | m2 , consist2 = (m1 ⊓M m2) , ConsistArr consist1 consist2

  ~D-dec : 
    (syn ana : Data) -> 
    ∃[ m ] syn ~D ana , m 
  ~D-dec □ _ = ✔ , ~DVoidL
  ~D-dec (■ syn) □ = ✔ , ~DVoidR
  ~D-dec (■ syn) (■ ana) with ~-dec syn ana 
  ... | m , consist = m , (~DSome consist)

  ~N-dec : 
    (syn ana : NewData) -> 
    ∃[ m ] syn ~N ana , m 
  ~N-dec (syn-d , syn-n) (ana-d , ana-n) with ~D-dec syn-d ana-d
  ... | m , consist = (m , (syn-n ⊓ ana-n)) , ~N-pair consist
  
  ▸DTArrow-unicity : ∀ {d t-in t-in' t-out t-out' m m'} ->
    d ▸DTArrow t-in , t-out , m -> 
    d ▸DTArrow t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸DTArrow-unicity DTArrowNone DTArrowNone = refl , refl , refl
  ▸DTArrow-unicity (DTArrowSome match1) (DTArrowSome match2) with ▸TArrow-unicity match1 match2
  ... | refl , refl , refl = refl , refl , refl

  ▸NTArrow-unicity : ∀ {d t-in t-in' t-out t-out' m m'} ->
    d ▸NTArrow t-in , t-out , m -> 
    d ▸NTArrow t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸NTArrow-unicity (NTArrowC match1) (NTArrowC match2) with ▸DTArrow-unicity match1 match2 
  ... | refl , refl , refl = refl , refl , refl

  ~D-unicity : ∀ {syn ana m m'} ->
    syn ~D ana , m -> 
    syn ~D ana , m' ->
    m ≡ m'
  ~D-unicity ~DVoidL ~DVoidL = refl
  ~D-unicity ~DVoidL ~DVoidR = refl
  ~D-unicity ~DVoidR ~DVoidL = refl
  ~D-unicity ~DVoidR ~DVoidR = refl
  ~D-unicity (~DSome consist1) (~DSome consist2) = ~-unicity consist1 consist2

  ~N-unicity : ∀ {syn ana m m'} ->
    syn ~N ana , m -> 
    syn ~N ana , m' ->
    m ≡ m'
  ~N-unicity (~N-pair consist1) (~N-pair consist2) rewrite ~D-unicity consist1 consist2 = refl

  -- not used
  -- ∈N-unicity : ∀ {x t t' Γ m m'} ->
  --   x , t ∈N Γ , m ->
  --   x , t' ∈N Γ , m' ->
  --   (t ≡ t' × m ≡ m')
  -- ∈N-unicity InCtxEmpty InCtxEmpty = refl , refl
  -- ∈N-unicity InCtxFound InCtxFound = refl , refl
  -- ∈N-unicity InCtxFound (InCtxSkip neq _) = ⊥-elim (neq refl)
  -- ∈N-unicity (InCtxSkip neq _) InCtxFound = ⊥-elim (neq refl)
  -- ∈N-unicity (InCtxSkip neq in-ctx) (InCtxSkip neq' in-ctx') = ∈N-unicity in-ctx in-ctx'

  beyond-▸NTArrow : ∀ {syn syn' t-in t-in' t-out t-out' m m'} ->
    =▷ syn syn' ->
    syn ▸NTArrow t-in , t-out , m -> 
    syn' ▸NTArrow t-in' , t-out' , m' -> 
    (=▷ t-in t-in' × =▷ t-out t-out' × =▷ m m')
  beyond-▸NTArrow =▷New (NTArrowC _) (NTArrowC _) = =▷New , =▷New , =▷New
  beyond-▸NTArrow =▷Refl (NTArrowC match1) (NTArrowC match2) with ▸DTArrow-unicity match1 match2 
  ... | refl , refl , refl = =▷Refl , =▷Refl , =▷Refl

  NUnless-new : ∀ {d n t} ->
    NUnless (d , n) (t , New) ≡ (DUnless d t , New)
  NUnless-new {n = n} {t = □} rewrite max-new n = refl 
  NUnless-new {t = ■ x} = refl  

  NUnless-new-▷ : ∀ {d n t d'} ->
    ▷ (NUnless (d , n) (t , New)) d'
  NUnless-new-▷ {d} {n} {t} rewrite NUnless-new {d} {n} {t} = ▷Pair ▶New

  beyond-▶ : 
    {A : Set} -> 
    {a a' : NEW A} 
    {b : A} ->
    =▷ a a' ->
    ▶ a b ->
    ▶ a' b 
  beyond-▶ =▷New consist = ▶New
  beyond-▶ =▷Refl consist = consist

  beyond-▷ : 
    {A : Set} -> 
    {a a' b : NEW A} ->
    =▷ a a' ->
    ▷ a b ->
    ▷ a' b 
  beyond-▷ =▷New consist = ▷Pair ▶New
  beyond-▷ =▷Refl consist = consist

  beyond-through-~N : ∀ {syn syn' ana m m'} ->
    =▷ syn syn' ->
    syn ~N ana , m -> 
    syn' ~N ana , m' ->
    =▷ m m'
  beyond-through-~N =▷New consist1 (~N-pair consist2) = =▷New
  beyond-through-~N =▷Refl consist1 consist2 rewrite ~N-unicity consist1 consist2 = =▷Refl

  preservation-lambda-lemma : ∀ {t syn1 syn1' syn2 ana} ->
    =▷ syn1 syn1' ->
    ▷ (NUnless (NArrow t syn1) ana) syn2 ->
    ▷ (NUnless (NArrow t syn1') ana) syn2
  preservation-lambda-lemma {t = t , n} {ana = □ , n-ana} =▷New (▷Pair consist) rewrite max-new n = ▷Pair ▶New
  preservation-lambda-lemma {t = t , n} {ana = ■ ana , n-ana} =▷New (▷Pair consist) = ▷Pair consist
  preservation-lambda-lemma {t = t , n} =▷Refl consist = consist

  consist-unless-lemma : ∀ {t1 t2 n1 n2 d} ->
    ▷ (NUnless (NArrow (t1 , n1) (t2 , n2)) (d , Old))
      (DUnless (DArrow t1 t2) d , New)
  consist-unless-lemma {d = □} = ▷Pair ▶Same
  consist-unless-lemma {d = ■ d} = ▷Pair ▶Old

  beyond-▷-contra : 
    {A : Set} -> 
    {a b b' : NEW A} ->
    ◁▷ b b' ->
    ▷ a b ->
    ▷ a b' 
  beyond-▷-contra ◁▷C (▷Pair consist) = ▷Pair consist

  l-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε L⟦ e-in ⟧M≡ e ->
    ε L⟦ e-in' ⟧M≡ e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  l-env-subsumable (FillLEnvFun _) (FillLEnvFun _) ()
  l-env-subsumable (FillLEnvAp1 _) (FillLEnvAp1 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillLEnvAp2 _) (FillLEnvAp2 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillLEnvAsc _) (FillLEnvAsc _) SubsumableAsc = SubsumableAsc

  u-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε U⟦ e-in ⟧M≡ e ->
    ε U⟦ e-in' ⟧M≡ e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  u-env-subsumable (FillUEnvFun _) (FillUEnvFun _) ()
  u-env-subsumable (FillUEnvAp1 _) (FillUEnvAp1 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillUEnvAp2 _) (FillUEnvAp2 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillUEnvAsc _) (FillUEnvAsc _) SubsumableAsc = SubsumableAsc

  oldify-syn : ∀ {Γ e t n n'} ->
    Γ U⊢ (e ⇒ (t , n)) ->
    Γ U⊢ (e ⇒ (t , n'))
  oldify-syn (WTConst (▷Pair consist)) = WTConst (▷Pair consist) 
  oldify-syn (WTHole (▷Pair consist)) = WTHole (▷Pair consist)
  oldify-syn (WTAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana) = WTAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana
  oldify-syn (WTVar in-ctx (▷Pair consist)) = WTVar in-ctx (▷Pair consist)
  oldify-syn (WTAsc (▷Pair consist-syn) consist-ana ana) = WTAsc (▷Pair consist-syn) consist-ana ana

  oldify-syn-inner : ∀ {Γ e t m n n'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , n')) ->
    Γ L⊢ ((e ⇒ (t , Old)) [ ✔ ]⇐ (□ , n'))
  oldify-syn-inner (WTUp subsumable (~N-pair consist) consist-m syn) = WTUp subsumable (~N-pair ~DVoidR) ▶Same (oldify-syn syn)
  oldify-syn-inner (WTFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ x₅ x₆ x₇ syn) = WTFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ (beyond-▷-contra ◁▷C x₅) (~N-pair ~DVoidR) ▶Same syn

  newify-ana : ∀ {Γ e n n' m m' ana t t'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ ana) -> 
    Γ L⊢ ((e ⇒ (t , n')) [ m' ]⇐ (t' , New))
  newify-ana {n' = n'} {t = t} {t' = t'} (WTUp {syn-all = syn-all} subsumable consist-t consist-m syn) with ~N-dec (t , n') (t' , New)
  ... | _ , (~N-pair consist-t') = WTUp subsumable (~N-pair consist-t') ▶New-max-r (oldify-syn syn)
  newify-ana {t = t} {t' = t'} (WTFun {syn-all = syn-all} {syn-body = syn-body , n-body} {t-asc = t-asc , n-asc} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ▸NTArrow-dec (t' , New)
  ... | (t-in , New) , (t-out , New) , (m , New) , NTArrowC marrow with ~N-dec (■ t-asc , n-asc) (t-in , New) | ~N-dec (t , New) (t' , New)
  ... | m' , consist | _ , ~N-pair consist' with new-through-~N-left consist 
  ... | _ , refl = WTFun (NTArrowC marrow) (■~N-pair consist) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ (~N-pair consist') ▶New-max-r ana

  small-newify-ana : ∀ {Γ e m m' ana t} ->
    Γ L⊢ (e [ m ]⇐ ana) -> 
    Γ L⊢ (e [ m' ]⇐ (t , New))
  small-newify-ana {e = e ⇒ (t , n)} ana = newify-ana ana

  data NewerCtx : Ctx -> Ctx -> Set where  
    NewerCtxRefl : ∀{Γ} ->
       NewerCtx Γ Γ
    NewerCtxInit : ∀{x t t' Γ} ->
       NewerCtx (x ∶ (t' , New) ∷ Γ) (x ∶ t ∷ Γ) 
    NewerCtxCons : ∀{x t Γ Γ'} ->
       NewerCtx Γ Γ' -> 
       NewerCtx (x ∶ t ∷ Γ) (x ∶ t ∷ Γ')

  NewerCtxInit? : ∀{x t t' Γ} ->
    NewerCtx (x ∶ (t' , New) ∷? Γ) (x ∶ t ∷? Γ)  
  NewerCtxInit? {BHole} = NewerCtxRefl
  NewerCtxInit? {BVar x} = NewerCtxInit

  NewerCtxCons? : ∀{x t Γ Γ'} ->
    NewerCtx Γ Γ' -> 
    NewerCtx (x ∶ t ∷? Γ) (x ∶ t ∷? Γ')
  NewerCtxCons? {BHole} newer = newer 
  NewerCtxCons? {BVar x} = NewerCtxCons
  
  newer-ctx-lookup : ∀{Γ Γ' x t m} ->
    NewerCtx Γ Γ' -> 
    x , t ∈N Γ' , m ->
    ∃[ t' ] (x , t' ∈N Γ , m) × (=▷ t t')
  newer-ctx-lookup NewerCtxRefl in-ctx = _ , in-ctx , =▷Refl
  newer-ctx-lookup NewerCtxInit InCtxFound = _ , InCtxFound , =▷New
  newer-ctx-lookup NewerCtxInit (InCtxSkip x in-ctx) = _ , InCtxSkip x in-ctx , =▷Refl
  newer-ctx-lookup (NewerCtxCons newer) InCtxFound = _ , InCtxFound , =▷Refl
  newer-ctx-lookup (NewerCtxCons newer) (InCtxSkip x in-ctx) with newer-ctx-lookup newer in-ctx 
  ... | t' , in-ctx' , beyond = _ , InCtxSkip x in-ctx' , beyond

  mutual 

    newer-ctx-u : ∀{Γ Γ' e} ->
      NewerCtx Γ Γ' -> 
      Γ' U⊢ e ->
      Γ U⊢ e
    newer-ctx-u newer (WTConst x) = WTConst x
    newer-ctx-u newer (WTHole x) = WTHole x
    newer-ctx-u newer (WTAp x x₁ x₂ x₃ x₄ x₅) = WTAp x x₁ x₂ x₃ (newer-ctx-l newer x₄) (newer-ctx-l newer x₅)
    newer-ctx-u newer (WTAsc x x₁ x₂) = WTAsc x x₁ (newer-ctx-l newer x₂)
    newer-ctx-u newer (WTVar x x₁) with newer-ctx-lookup newer x 
    ... | t' , in-ctx' , beyond = WTVar in-ctx' (beyond-▷ beyond x₁)

    newer-ctx-l : ∀{Γ Γ' e} ->
      NewerCtx Γ Γ' -> 
      Γ' L⊢ e ->
      Γ L⊢ e
    newer-ctx-l newer (WTUp x x₁ x₂ x₃) = WTUp x x₁ x₂ (newer-ctx-u newer x₃)
    newer-ctx-l newer (WTFun {x = x} x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ wt) = WTFun x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ (newer-ctx-l (NewerCtxCons? {x} newer) wt)
 
  newify-ctx : ∀{Γ x t t' e} ->
    (x ∶ t ∷? Γ) L⊢ e -> 
    (x ∶ (t' , New) ∷? Γ) L⊢ e     
  newify-ctx {x = x} = newer-ctx-l (NewerCtxInit? {x})