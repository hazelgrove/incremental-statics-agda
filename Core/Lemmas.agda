
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.SideConditions
open import Core.Environment
open import Core.WellFormed
open import Core.MarkingUnicity

module Core.Lemmas where

  data =▷ {A : Set} : ○ A -> ○ A -> Set where 
    =▷★ : ∀ {s t} -> 
      =▷ s (t , ★)
    =▷Refl : ∀ {s} -> 
      =▷ s s

  data ◁▷ {A : Set} : ○ A -> ○ A -> Set where 
    ◁▷C : ∀ {t n n'} -> 
      ◁▷ (t , n) (t , n')

  max-dirty : (n : Dirtiness) -> n ⊓ ★ ≡ ★ 
  max-dirty • = refl
  max-dirty ★ = refl

  ~DVoid-right : ∀ {t m} ->
    t ~D □ , m ->
    m ≡ ✔
  ~DVoid-right ~DVoidL = refl
  ~DVoid-right ~DVoidR = refl

  ~D-unless : ∀ {t1 t2} ->
    DUnless t1 t2 ~D t2 , ✔
  ~D-unless {t2 = □} = ~DVoidR
  ~D-unless {t2 = ■ x} = ~DVoidL 

  dirty-through-~N-left : ∀ {d t m} ->
    d ~N (t , ★) , m -> 
    ∃[ m' ] m ≡ (m' , ★)
  dirty-through-~N-left (~N-pair {n1 = n1} consist) rewrite max-dirty n1 = _ , refl

  ▶Same : ∀ {n} ->
    {A : Set} ->
    {a : A} ->
    ▶ (a , n) a
  ▶Same {•} = ▶•
  ▶Same {★} = ▶★

  ▶★-max-r : ∀ {n} -> 
    {A : Set} -> 
    {a a' : A} ->
    ▶ (a , (n ⊓ ★)) a'
  ▶★-max-r {n = n} rewrite max-dirty n = ▶★

  -- ▸TArrow-dec : 
  --   (t : Type) -> 
  --   ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸TArrow t-in , t-out , m
  -- ▸TArrow-dec TBase = THole , THole , ✖ , MArrowBase
  -- ▸TArrow-dec THole = THole , THole , ✔ , MArrowHole
  -- ▸TArrow-dec (TArrow t1 t2) = t1 , t2 , ✔ , MArrowArrow
  -- ▸TArrow-dec (TProd t1 t2) = THole , THole , ✖ , MArrowProd

  ▸DTArrow-dec : 
    (t : Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸DTArrow t-in , t-out , m
  ▸DTArrow-dec □ = □ , □ , ✔ , DTArrowNone
  ▸DTArrow-dec (■ t) with ▸TArrow-dec t 
  ... | t1 , t2 , m , match = ■ t1 , ■ t2 , m , DTArrowSome match

  ▸NTArrow-dec : 
    (d : ○Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] d ▸NTArrow t-in , t-out , m
  ▸NTArrow-dec (d , n) with ▸DTArrow-dec d 
  ... | t1 , t2 , m , match = (t1 , n) , (t2 , n) , (m , n) , NTArrowC match

  -- ▸TProd-dec : 
  --   (t : Type) -> 
  --   ∃[ t-fst ] ∃[ t-snd ] ∃[ m ] t ▸TProd t-fst , t-snd , m
  -- ▸TProd-dec TBase = THole , THole , ✖ , MProdBase
  -- ▸TProd-dec THole = THole , THole , ✔ , MProdHole
  -- ▸TProd-dec (TArrow t t₁) = THole , THole , ✖ , MProdArrow
  -- ▸TProd-dec (TProd t t₁) = t , t₁ , ✔ , MProdProd

  ▸DTProd-dec : 
    (t : Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸DTProd t-in , t-out , m
  ▸DTProd-dec □ = □ , □ , ✔ , DTProdNone
  ▸DTProd-dec (■ t) with ▸TProd-dec t 
  ... | t1 , t2 , m , match = ■ t1 , ■ t2 , m , DTProdSome match

  ▸NTProd-dec : 
    (d : ○Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] d ▸NTProd t-in , t-out , m
  ▸NTProd-dec (d , n) with ▸DTProd-dec d 
  ... | t1 , t2 , m , match = (t1 , n) , (t2 , n) , (m , n) , NTProdC match
  
  -- ▸TProj-dec : 
  --   (s : ProdSide) -> 
  --   (t : Type) -> 
  --   ∃[ t' ] ∃[ m ] t , s ▸TProj t' , m
  -- ▸TProj-dec Fst TBase = THole , ✖ , MProdFst MProdBase
  -- ▸TProj-dec Fst THole = THole , ✔ , MProdFst MProdHole
  -- ▸TProj-dec Fst (TArrow t t₁) = THole , ✖ , MProdFst MProdArrow
  -- ▸TProj-dec Fst (TProd t t₁) = t , ✔ , MProdFst MProdProd
  -- ▸TProj-dec Snd TBase = THole , ✖ , MProdSnd MProdBase
  -- ▸TProj-dec Snd THole = THole , ✔ , MProdSnd MProdHole
  -- ▸TProj-dec Snd (TArrow t t₁) = THole , ✖ , MProdSnd MProdArrow
  -- ▸TProj-dec Snd (TProd t t₁) = t₁ , ✔ , MProdSnd MProdProd

  ▸DTProj-dec : 
    (s : ProdSide) -> 
    (t : Data) -> 
    ∃[ t' ] ∃[ m ] t , s ▸DTProj t' , m
  ▸DTProj-dec s □ = □ , ✔ , DTProjNone
  ▸DTProj-dec s (■ t) with ▸TProj-dec s t 
  ... | t' , m , match = ■ t' , m , DTProjSome match

  ▸NTProj-dec : 
    (s : ProdSide) -> 
    (d : ○Data) -> 
    ∃[ t ] ∃[ m ] d , s ▸NTProj t , m
  ▸NTProj-dec s (d , n) with ▸DTProj-dec s d 
  ... | t , m , match = (t , n) , (m , n) , NTProjC match

  -- ~-dec : 
  --   (syn ana : Type) -> 
  --   ∃[ m ] syn ~ ana , m 
  -- ~-dec THole _ = ✔ , ConsistHoleL
  -- ~-dec _ THole = ✔ , ConsistHoleR
  -- ~-dec TBase TBase = ✔ , ConsistBase
  -- ~-dec TBase (TArrow _ _) = ✖ , InconsistBaseArr
  -- ~-dec TBase (TProd _ _) = ✖ , InconsistBaseProd
  -- ~-dec (TArrow _ _) TBase = ✖ , InconsistArrBase
  -- ~-dec (TArrow syn1 syn2) (TArrow ana1 ana2) with ~-dec syn1 ana1 | ~-dec syn2 ana2 
  -- ... | m1 , consist1 | m2 , consist2 = (m1 ⊓M m2) , ConsistArr consist1 consist2
  -- ~-dec (TArrow _ _) (TProd _ _ ) = ✖ , InconsistArrProd 
  -- ~-dec (TProd t1 t2) TBase = ✖ , InconsistProdBase
  -- ~-dec (TProd t1 t2) (TArrow t3 t4) = ✖ , InconsistProdArr
  -- ~-dec (TProd t1 t2) (TProd t3 t4) with ~-dec t1 t3 | ~-dec t2 t4 
  -- ... | m1 , consist1 | m2 , consist2 = (m1 ⊓M m2) , ConsistProd consist1 consist2

  ~D-dec : 
    (syn ana : Data) -> 
    ∃[ m ] syn ~D ana , m 
  ~D-dec □ _ = ✔ , ~DVoidL
  ~D-dec (■ syn) □ = ✔ , ~DVoidR
  ~D-dec (■ syn) (■ ana) with ~-dec syn ana 
  ... | m , consist = m , (~DSome consist)

  ~N-dec : 
    (syn ana : ○Data) -> 
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

  ▸DTProd-unicity : ∀ {d t-in t-in' t-out t-out' m m'} ->
    d ▸DTProd t-in , t-out , m -> 
    d ▸DTProd t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸DTProd-unicity DTProdNone DTProdNone = refl , refl , refl
  ▸DTProd-unicity (DTProdSome match1) (DTProdSome match2) with ▸TProd-unicity match1 match2
  ... | refl , refl , refl = refl , refl , refl
  
  ▸DTProj-unicity : ∀ {d s t t' m m'} ->
    d , s ▸DTProj t , m -> 
    d , s ▸DTProj t' , m' -> 
    (t ≡ t' × m ≡ m')
  ▸DTProj-unicity DTProjNone DTProjNone = refl , refl
  ▸DTProj-unicity (DTProjSome match1) (DTProjSome match2) with ▸TProj-unicity match1 match2
  ... | refl , refl = refl , refl

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
  beyond-▸NTArrow =▷★ (NTArrowC _) (NTArrowC _) = =▷★ , =▷★ , =▷★
  beyond-▸NTArrow =▷Refl (NTArrowC match1) (NTArrowC match2) with ▸DTArrow-unicity match1 match2 
  ... | refl , refl , refl = =▷Refl , =▷Refl , =▷Refl

  beyond-▸NTProj : ∀ {syn syn' s t t' m m'} ->
    =▷ syn syn' ->
    syn , s ▸NTProj t , m -> 
    syn' , s ▸NTProj t' , m' -> 
    (=▷ t t' × =▷ m m')
  beyond-▸NTProj =▷★ (NTProjC x) (NTProjC x₁) = =▷★ , =▷★
  beyond-▸NTProj =▷Refl (NTProjC x) (NTProjC x₁) with ▸DTProj-unicity x x₁ 
  ... | refl , refl = =▷Refl , =▷Refl

  NUnless-dirty : ∀ {d n t} ->
    NUnless (d , n) (t , ★) ≡ (DUnless d t , ★)
  NUnless-dirty {n = n} {t = □} rewrite max-dirty n = refl 
  NUnless-dirty {t = ■ x} = refl  

  NUnless-dirty-▷ : ∀ {d n t d'} ->
    ▷ (NUnless (d , n) (t , ★)) d'
  NUnless-dirty-▷ {d} {n} {t} rewrite NUnless-dirty {d} {n} {t} = ▷Pair ▶★

  beyond-▶ : 
    {A : Set} -> 
    {a a' : ○ A} 
    {b : A} ->
    =▷ a a' ->
    ▶ a b ->
    ▶ a' b 
  beyond-▶ =▷★ consist = ▶★
  beyond-▶ =▷Refl consist = consist

  beyond-▷ : 
    {A : Set} -> 
    {a a' b : ○ A} ->
    =▷ a a' ->
    ▷ a b ->
    ▷ a' b 
  beyond-▷ =▷★ consist = ▷Pair ▶★
  beyond-▷ =▷Refl consist = consist

  beyond-through-~N : ∀ {syn syn' ana m m'} ->
    =▷ syn syn' ->
    syn ~N ana , m -> 
    syn' ~N ana , m' ->
    =▷ m m'
  beyond-through-~N =▷★ consist1 (~N-pair consist2) = =▷★
  beyond-through-~N =▷Refl consist1 consist2 rewrite ~N-unicity consist1 consist2 = =▷Refl

  preservation-lambda-lemma : ∀ {t syn1 syn1' syn2 ana} ->
    =▷ syn1 syn1' ->
    ▷ (NUnless (NArrow t syn1) ana) syn2 ->
    ▷ (NUnless (NArrow t syn1') ana) syn2
  preservation-lambda-lemma {t = t , n} {ana = □ , n-ana} =▷★ (▷Pair consist) rewrite max-dirty n = ▷Pair ▶★
  preservation-lambda-lemma {t = t , n} {ana = ■ ana , n-ana} =▷★ (▷Pair consist) = ▷Pair consist
  preservation-lambda-lemma {t = t , n} =▷Refl consist = consist

  consist-unless-lemma : ∀ {t1 t2 n1 n2 d} ->
    ▷ (NUnless (NArrow (t1 , n1) (t2 , n2)) (d , •))
      (DUnless (DArrow t1 t2) d , ★)
  consist-unless-lemma {d = □} = ▷Pair ▶Same
  consist-unless-lemma {d = ■ d} = ▷Pair ▶•

  consist-unless-prod : ∀ {t1 t2 n1 n2 d} ->
    ▷ (NUnless (NProd (t1 , n1) (t2 , n2)) (d , •))
      (DUnless (DProd t1 t2) d , ★)
  consist-unless-prod {d = □} = ▷Pair ▶Same
  consist-unless-prod {d = ■ d} = ▷Pair ▶•

  preservation-pair-lemma : ∀ {syn1 syn1' syn2 syn2' ana syn-all} ->
    =▷ syn1 syn1' ->
    =▷ syn2 syn2' ->
    ▷ (NUnless (NProd syn1 syn2) ana) syn-all ->
    ▷ (NUnless (NProd syn1' syn2') ana) syn-all
  preservation-pair-lemma {ana = □ , n-ana} =▷★ =▷★ (▷Pair consist) = ▷Pair ▶★
  preservation-pair-lemma {ana = ■ ana , n-ana} =▷★ =▷★ (▷Pair consist) = ▷Pair consist
  preservation-pair-lemma {ana = □ , n-ana} =▷★ =▷Refl (▷Pair consist) = ▷Pair ▶★
  preservation-pair-lemma {ana = ■ ana , n-ana} =▷★ =▷Refl (▷Pair consist) = ▷Pair consist
  preservation-pair-lemma {syn1 = syn1 , n1} {ana = □ , n-ana} =▷Refl =▷★ (▷Pair consist) rewrite max-dirty n1 = ▷Pair ▶★
  preservation-pair-lemma {syn1 = syn1 , n1} {ana = ■ ana , n-ana} =▷Refl =▷★ (▷Pair consist) = ▷Pair consist
  preservation-pair-lemma =▷Refl =▷Refl consist = consist

  beyond-▷-contra : 
    {A : Set} -> 
    {a b b' : ○ A} ->
    ◁▷ b b' ->
    ▷ a b ->
    ▷ a b' 
  beyond-▷-contra ◁▷C (▷Pair consist) = ▷Pair consist

  l-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε A⟦ e-in ⟧C≡ e ->
    ε A⟦ e-in' ⟧C≡ e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  l-env-subsumable (FillAnaEnvFun _) (FillAnaEnvFun _) ()
  l-env-subsumable (FillAnaEnvAp1 _) (FillAnaEnvAp1 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillAnaEnvAp2 _) (FillAnaEnvAp2 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillAnaEnvAsc _) (FillAnaEnvAsc _) SubsumableAsc = SubsumableAsc
  l-env-subsumable (FillAnaEnvProj _) (FillAnaEnvProj _) SubsumableProj = SubsumableProj

  u-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε S⟦ e-in ⟧C≡ e ->
    ε S⟦ e-in' ⟧C≡ e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  u-env-subsumable (FillSynEnvFun _) (FillSynEnvFun _) ()
  u-env-subsumable (FillSynEnvAp1 _) (FillSynEnvAp1 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillSynEnvAp2 _) (FillSynEnvAp2 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillSynEnvAsc _) (FillSynEnvAsc _) SubsumableAsc = SubsumableAsc
  u-env-subsumable (FillSynEnvProj _) (FillSynEnvProj _) SubsumableProj = SubsumableProj

  oldify-syn : ∀ {Γ e t n n'} ->
    Γ S⊢ (e ⇒ (t , n)) ->
    Γ S⊢ (e ⇒ (t , n'))
  oldify-syn (WFConst (▷Pair consist)) = WFConst (▷Pair consist) 
  oldify-syn (WFHole (▷Pair consist)) = WFHole (▷Pair consist)
  oldify-syn (WFAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana) = WFAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana
  oldify-syn (WFVar in-ctx (▷Pair consist)) = WFVar in-ctx (▷Pair consist)
  oldify-syn (WFAsc (▷Pair consist-syn) consist-ana ana) = WFAsc (▷Pair consist-syn) consist-ana ana
  oldify-syn (WFProj x (▷Pair x₁) x₂ x₃) = WFProj x (▷Pair x₁) x₂ x₃

  oldify-syn-inner : ∀ {Γ e t m n n'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , n')) ->
    Γ L⊢ ((e ⇒ (t , •)) [ ✔ ]⇐ (□ , n'))
  oldify-syn-inner (WFSubsume subsumable (~N-pair consist) consist-m syn) = WFSubsume subsumable (~N-pair ~DVoidR) ▶Same (oldify-syn syn)
  oldify-syn-inner (WFFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ x₅ x₆ x₇ syn) = WFFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ (beyond-▷-contra ◁▷C x₅) (~N-pair ~DVoidR) ▶Same syn
  oldify-syn-inner (WFPair (NTProdC DTProdNone) (▷Pair x) (▷Pair x₁) x₃ x₄ x₅ x₆ w w₁) = WFPair (NTProdC DTProdNone) (▷Pair x) (▷Pair x₁) x₃ (beyond-▷-contra ◁▷C x₄) (~N-pair ~DVoidR) ▶Same w w₁

  dirty-syn-inner : ∀ {Γ e n m m' ana t} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ ana) -> 
    Γ L⊢ ((e ⇒ (t , ★)) [ m' ]⇐ ana)
  dirty-syn-inner (WFSubsume x (~N-pair x₁) x₂ x₃) = WFSubsume x (~N-pair x₁) ▶★ (oldify-syn x₃)
  dirty-syn-inner (WFFun x x₁ x₂ x₃ x₄ (▷Pair x₅) (~N-pair x₆) x₇ wt) = WFFun x x₁ x₂ x₃ x₄ (▷Pair x₅) (~N-pair x₆) ▶★ wt
  dirty-syn-inner (WFPair (NTProdC y) (▷Pair x) (▷Pair x₁) x₃ x₄ (~N-pair x₅) x₆ w w₁) = WFPair (NTProdC y) (▷Pair x) (▷Pair x₁) x₃ (beyond-▷-contra ◁▷C x₄) (~N-pair x₅) ▶★ w w₁

  dirty-ana : ∀ {Γ e n n' m m' ana t t'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ ana) -> 
    Γ L⊢ ((e ⇒ (t , n')) [ m' ]⇐ (t' , ★))
  dirty-ana {n' = n'} {t = t} {t' = t'} (WFSubsume {syn-all = syn-all} subsumable consist-t consist-m syn) with ~N-dec (t , n') (t' , ★)
  ... | _ , (~N-pair consist-t') = WFSubsume subsumable (~N-pair consist-t') ▶★-max-r (oldify-syn syn)
  dirty-ana {t = t} {t' = t'} (WFFun {syn-all = syn-all} {syn-body = syn-body , n-body} {t-asc = t-asc , n-asc} (NTArrowC _) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ▸NTArrow-dec (t' , ★)
  ... | (t-in , ★) , (t-out , ★) , (m , ★) , NTArrowC marrow with ~N-dec (■ t-asc , n-asc) (t-in , ★) | ~N-dec (t , ★) (t' , ★)
  ... | m' , consist | _ , ~N-pair consist' with dirty-through-~N-left consist 
  ... | _ , refl = WFFun (NTArrowC marrow) (■~N-pair consist) (▷Pair ▶★) ▶★ ▶★ NUnless-dirty-▷ (~N-pair consist') ▶★-max-r ana
  dirty-ana {t = t} {t' = t'} (WFPair (NTProdC y) (▷Pair x) (▷Pair x₁) x₃ x₄ (~N-pair x₅) x₆ w w₁) with ▸NTProd-dec (t' , ★)
  ... | (t-fst , ★) , (t-snd , ★) , (m , ★) , NTProdC marrow with ~N-dec (t , ★) (t' , ★)
  ... | _ , ~N-pair consist' = WFPair (NTProdC marrow) (▷Pair ▶★) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair consist') ▶★-max-r w w₁

  small-dirty-ana : ∀ {Γ e m m' ana t} ->
    Γ L⊢ (e [ m ]⇐ ana) -> 
    Γ L⊢ (e [ m' ]⇐ (t , ★))
  small-dirty-ana {e = e ⇒ (t , n)} ana = dirty-ana ana


  data ★erCtx : Ctx -> Ctx -> Set where  
    ★erCtxRefl : ∀{Γ} ->
       ★erCtx Γ Γ
    ★erCtxInit : ∀{x t t' Γ} ->
       ★erCtx (x ∶ (t' , ★) ∷ Γ) (x ∶ t ∷ Γ) 
    ★erCtxCons : ∀{x t Γ Γ'} ->
       ★erCtx Γ Γ' -> 
       ★erCtx (x ∶ t ∷ Γ) (x ∶ t ∷ Γ')

  ★erCtxInit? : ∀{x t t' Γ} ->
    ★erCtx (x ∶ (t' , ★) ∷? Γ) (x ∶ t ∷? Γ)  
  ★erCtxInit? {BHole} = ★erCtxRefl
  ★erCtxInit? {BVar x} = ★erCtxInit

  ★erCtxCons? : ∀{x t Γ Γ'} ->
    ★erCtx Γ Γ' -> 
    ★erCtx (x ∶ t ∷? Γ) (x ∶ t ∷? Γ')
  ★erCtxCons? {BHole} dirtyer = dirtyer 
  ★erCtxCons? {BVar x} = ★erCtxCons
  
  dirtyer-ctx-lookup : ∀{Γ Γ' x t m} ->
    ★erCtx Γ Γ' -> 
    x , t ∈N Γ' , m ->
    ∃[ t' ] (x , t' ∈N Γ , m) × (=▷ t t')
  dirtyer-ctx-lookup ★erCtxRefl in-ctx = _ , in-ctx , =▷Refl
  dirtyer-ctx-lookup ★erCtxInit InCtxFound = _ , InCtxFound , =▷★
  dirtyer-ctx-lookup ★erCtxInit (InCtxSkip x in-ctx) = _ , InCtxSkip x in-ctx , =▷Refl
  dirtyer-ctx-lookup (★erCtxCons dirtyer) InCtxFound = _ , InCtxFound , =▷Refl
  dirtyer-ctx-lookup (★erCtxCons dirtyer) (InCtxSkip x in-ctx) with dirtyer-ctx-lookup dirtyer in-ctx 
  ... | t' , in-ctx' , beyond = _ , InCtxSkip x in-ctx' , beyond

  mutual 

    dirtyer-ctx-u : ∀{Γ Γ' e} ->
      ★erCtx Γ Γ' -> 
      Γ' S⊢ e ->
      Γ S⊢ e
    dirtyer-ctx-u dirtyer (WFConst x) = WFConst x
    dirtyer-ctx-u dirtyer (WFHole x) = WFHole x
    dirtyer-ctx-u dirtyer (WFAp x x₁ x₂ x₃ x₄ x₅) = WFAp x x₁ x₂ x₃ (dirtyer-ctx-l dirtyer x₄) (dirtyer-ctx-l dirtyer x₅)
    dirtyer-ctx-u dirtyer (WFAsc x x₁ x₂) = WFAsc x x₁ (dirtyer-ctx-l dirtyer x₂)
    dirtyer-ctx-u dirtyer (WFVar x x₁) with dirtyer-ctx-lookup dirtyer x 
    ... | t' , in-ctx' , beyond = WFVar in-ctx' (beyond-▷ beyond x₁)
    dirtyer-ctx-u dirtyer (WFProj x x₁ x₂ x₃) = WFProj x x₁ x₂ (dirtyer-ctx-l dirtyer x₃)

    dirtyer-ctx-l : ∀{Γ Γ' e} ->
      ★erCtx Γ Γ' -> 
      Γ' L⊢ e ->
      Γ L⊢ e
    dirtyer-ctx-l dirtyer (WFSubsume x x₁ x₂ x₃) = WFSubsume x x₁ x₂ (dirtyer-ctx-u dirtyer x₃)
    dirtyer-ctx-l dirtyer (WFFun {x = x} x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ wt) = WFFun x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ (dirtyer-ctx-l (★erCtxCons? {x} dirtyer) wt)
    dirtyer-ctx-l dirtyer (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (dirtyer-ctx-l dirtyer wt) (dirtyer-ctx-l dirtyer wt₁)
 
  dirty-ctx : ∀{Γ x t t' e} ->  
    (x ∶ t ∷? Γ) L⊢ e ->  
    (x ∶ (t' , ★) ∷? Γ) L⊢ e        
  dirty-ctx {x = x} = dirtyer-ctx-l (★erCtxInit? {x})