
open import Data.Nat hiding (_+_; _⊓_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment
open import Core.WellTyped
open import Core.VarsSynthesize
open import Core.MarkingUnicity

module Core.Lemmas-Preservation where

  -- oldify-ntmatch : ∀ {t n t1 t2 m n1 n2 n3} ->
  --   (t , n) ▸NTArrow (t1 , n1) , (t2 , n2) , (m , n3) ->
  --   (t , Old) ▸NTArrow (t1 , Old) , (t2 , Old) , (m , MarkOld)
  -- oldify-ntmatch (MNTArrowOldMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowOldNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch (MNTArrowNewMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowNewNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch MNTArrowArrow = MNTArrowOldMatch MArrowArrow

  -- the "beyondness" relation - the latter is the unchanged or [New]
  data =▷ {A : Set} : NEW A -> NEW A -> Set where 
    =▷New : ∀ {s t} -> 
      =▷ s (t , New)
    =▷Refl : ∀ {s} -> 
      =▷ s s

  -- stays the same, or becomes old
  data ◁= {A : Set} : NEW A -> NEW A -> Set where 
    ◁=Old : ∀ {t t' n} -> 
      ◁= (t , n) (t' , Old)
    ◁=Refl : ∀ {t} -> ◁= t t

  data ◁▷ {A : Set} : NEW A -> NEW A -> Set where 
    ◁▷C : ∀ {t n n'} -> 
      ◁▷ (t , n) (t , n')

  max-new : (n : Newness) -> n ⊓ New ≡ New 
  max-new Old = refl
  max-new New = refl

  max-old : (n : Newness) -> n ⊓ Old ≡ n 
  max-old Old = refl
  max-old New = refl

  ~DVoid-right : ∀ {t m} ->
    t ~D □ , m ->
    m ≡ ✔
  ~DVoid-right ~DVoidL = refl
  ~DVoid-right ~DVoidR = refl

  ~D-unless : ∀ {t1 t2} ->
    DUnless t1 t2 ~D t2 , ✔
  ~D-unless {t2 = □} = ~DVoidR
  ~D-unless {t2 = ■ x} = ~DVoidL 

  -- ▷New : {A : Set} -> {t : A} -> {n : NEW A} ->
  --   ▷ (t , New) n 
  -- ▷New = ▷Pair ▶New
  
  -- -- ▷D-new : ∀ {t syn} -> ▷D (■ (t , New)) syn
  -- -- ▷D-new {syn = □} = ▷DVoidR
  -- -- ▷D-new {syn = ■ (t , n)} = ▷DSome MergeInfoNew

  -- new-through-▸DTArrow : ∀ {t t-in t-out m} ->
  --   ■ (t , New) ▸DTArrow t-in , t-out , m -> 
  --   ∃[ t-in' ] ∃[ t-out' ] ∃[ m' ] (t-in ≡ (t-in' , New) × t-out ≡ (t-out' , New) × m ≡ (m' , New))
  -- new-through-▸DTArrow (SynArrowSome (MNTArrowNew x)) = _ , _ , _ , refl , refl , refl

  new-through-~N-left : ∀ {d t m} ->
    d ~N (t , New) , m -> 
    ∃[ m' ] m ≡ (m' , New)
  new-through-~N-left (~N-pair {n1 = n1} consist) rewrite max-new n1 = _ , refl

  new-through-~N-right : ∀ {d t m} ->
    (t , New) ~N d , m -> 
    ∃[ m' ] m ≡ (m' , New)
  new-through-~N-right (~N-pair consist) = _ , refl

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

  -- new-through-~D-right : ∀ {d t m} ->
  --   ■ (t , New) ~D d , m -> 
  --   ∃[ m' ] m ≡ (m' , New)
  -- new-through-~D-right ~DVoidR = ✔ , refl
  -- new-through-~D-right (~DSome (NMConsist {n1 = n1} x)) = _ , refl

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


  ∈N-unicity : ∀ {x t t' Γ m m'} ->
    x , t ∈N Γ , m ->
    x , t' ∈N Γ , m' ->
    (t ≡ t' × m ≡ m')
  ∈N-unicity InCtxEmpty InCtxEmpty = refl , refl
  ∈N-unicity InCtxFound InCtxFound = refl , refl
  ∈N-unicity InCtxFound (InCtxSkip neq _) = ⊥-elim (neq refl)
  ∈N-unicity (InCtxSkip neq _) InCtxFound = ⊥-elim (neq refl)
  ∈N-unicity (InCtxSkip neq in-ctx) (InCtxSkip neq' in-ctx') = ∈N-unicity in-ctx in-ctx'


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

  -- beyond-consist-m : ∀ {m1 m1' m2} ->
  --   =▷M m1 m1' ->
  --   ▷NM m1 m2 ->
  --   ▷NM m1' m2 
  -- beyond-consist-m =▷MNew consist = ▷NMNew
  -- beyond-consist-m ▷MRefl consist = consist

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

  -- -- new-beyond-through-~NM : ∀ {syn syn' ana m m'} ->
  -- --   =▷T syn syn' ->
  -- --   (t , New) ~NM ana , m -> 
  -- --   (t , Old) ~NM ana , m' ->
  -- --   =▷M m m'
  -- -- beyond-through-~NM = {!   !}

  beyond-through-~N : ∀ {syn syn' ana m m'} ->
    =▷ syn syn' ->
    syn ~N ana , m -> 
    syn' ~N ana , m' ->
    =▷ m m'
  beyond-through-~N =▷New consist1 consist2 with new-through-~N-right consist2 
  ... | m' , refl = =▷New
  beyond-through-~N =▷Refl consist1 consist2 rewrite ~N-unicity consist1 consist2 = =▷Refl

  preservation-lambda-lemma : ∀ {t syn1 syn1' syn2} ->
    =▷ syn1 syn1' ->
    ▷ (NArrow t syn1) syn2 ->
    ▷ (NArrow t syn1') syn2
  preservation-lambda-lemma {t = t , n} =▷New (▷Pair consist) rewrite max-new n = ▷Pair ▶New
  preservation-lambda-lemma =▷Refl consist = consist

  preservation-lambda-lemma-2 : ∀ {t1 t2 n syn} ->
    =▷ ((■ t2 , n)) syn -> 
    ▷ (NArrow (t1 , Old) syn) ((■ (TArrow t1 t2) , New))
  preservation-lambda-lemma-2 =▷New = ▷Pair ▶New 
  preservation-lambda-lemma-2 =▷Refl = ▷Pair ▶Same 

  preservation-lambda-lemma-3 : ∀ {t syn1 syn1' syn2 ana} ->
    =▷ syn1 syn1' ->
    ▷ (NUnless (NArrow t syn1) ana) syn2 ->
    ▷ (NUnless (NArrow t syn1') ana) syn2
  preservation-lambda-lemma-3 {t = t , n} {ana = □ , n-ana} =▷New (▷Pair consist) rewrite max-new n = ▷Pair ▶New
  preservation-lambda-lemma-3 {t = t , n} {ana = ■ ana , n-ana} =▷New (▷Pair consist) = ▷Pair consist
  preservation-lambda-lemma-3 {t = t , n} =▷Refl consist = consist

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

  beyond-▷■-contra : 
    ∀ {a b b'} ->
    ◁▷ b b' ->
    ▷■ a b ->
    ▷■ a b' 
  beyond-▷■-contra ◁▷C (▷■Pair (▷Pair consist)) = ▷■Pair (▷Pair consist)

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
  oldify-syn (SynConst (▷Pair consist)) = SynConst (▷Pair consist) 
  oldify-syn (SynHole (▷Pair consist)) = SynHole (▷Pair consist)
  oldify-syn (SynAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana) = SynAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana
  oldify-syn (SynVar in-ctx (▷Pair consist)) = SynVar in-ctx (▷Pair consist)
  oldify-syn (SynAsc (▷Pair consist-syn) consist-ana ana) = SynAsc (▷Pair consist-syn) consist-ana ana

  oldify-syn-inner : ∀ {Γ e t m n n'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , n')) ->
    Γ L⊢ ((e ⇒ (t , Old)) [ ✔ ]⇐ (□ , n'))
  oldify-syn-inner (AnaSubsume subsumable (~N-pair consist) consist-m syn) = AnaSubsume subsumable (~N-pair ~DVoidR) ▶Same (oldify-syn syn)
  oldify-syn-inner (AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ x₅ x₆ x₇ syn)  = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ (beyond-▷-contra ◁▷C x₅) (~N-pair ~DVoidR) ▶Same syn


  newify-ana : ∀ {Γ e n n' m m' ana t t'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ ana) -> 
    Γ L⊢ ((e ⇒ (t , n')) [ m' ]⇐ (t' , New))
  newify-ana {n' = n'} {t = t} {t' = t'} (AnaSubsume {syn-all = syn-all} subsumable consist-t consist-m syn) with ~N-dec (t , n') (t' , New)
  ... | _ , (~N-pair consist-t') = AnaSubsume subsumable (~N-pair consist-t') ▶New-max-r (oldify-syn syn)
  newify-ana {t = t} {t' = t'} (AnaFun {syn-all = syn-all} {syn-body = syn-body , n-body} {t-asc = t-asc , n-asc} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ▸NTArrow-dec (t' , New)
  ... | (t-in , New) , (t-out , New) , (m , New) , NTArrowC marrow with ~N-dec (■ t-asc , n-asc) (t-in , New) | ~N-dec (t , New) (t' , New)
  ... | m' , consist | _ , ~N-pair consist' with new-through-~N-left consist 
  ... | _ , refl = AnaFun (NTArrowC marrow) (■~N-pair consist) (▷Pair ▶New) ▶New ▶New NUnless-new-▷ (~N-pair consist') ▶New-max-r ana

  small-newify-ana : ∀ {Γ e m m' ana t} ->
    Γ L⊢ (e [ m ]⇐ ana) -> 
    Γ L⊢ (e [ m' ]⇐ (t , New))
  small-newify-ana {e = e ⇒ (t , n)} ana = newify-ana ana

  vars-syn-subsumable : ∀ {x t m e e' syn syn'} ->
    VarsSynthesize x t m (e ⇒ syn) (e' ⇒ syn') -> 
    SubsumableMid e ->
    SubsumableMid e'
  vars-syn-subsumable VSConst SubsumableConst = SubsumableConst
  vars-syn-subsumable VSHole SubsumableHole = SubsumableHole
  vars-syn-subsumable VSFunEq ()
  vars-syn-subsumable (VSFunNeq neq vars-syn) ()
  vars-syn-subsumable (VSAp vars-syn1 vars-syn2) SubsumableAp = SubsumableAp
  vars-syn-subsumable VSVarEq SubsumableVar = SubsumableVar
  vars-syn-subsumable (VSVarNeq _) SubsumableVar = SubsumableVar
  vars-syn-subsumable (VSAsc vars-syn) SubsumableAsc = SubsumableAsc

  vars-syn-beyond : ∀ {x t m e syn e' syn'} ->
    VarsSynthesize x t m (e ⇒ syn) (e' ⇒ syn') -> 
    =▷ syn syn' 
  vars-syn-beyond VSConst = =▷Refl
  vars-syn-beyond VSHole = =▷Refl
  vars-syn-beyond VSFunEq = =▷Refl
  vars-syn-beyond (VSFunNeq neq syn) = =▷Refl
  vars-syn-beyond (VSAp syn syn₁) = =▷Refl
  vars-syn-beyond VSVarEq = =▷New
  vars-syn-beyond (VSVarNeq x) = =▷Refl
  vars-syn-beyond (VSAsc syn) = =▷Refl

  vars-syn?-beyond : ∀ {x t m e syn e' syn'} ->
    VarsSynthesize? x t m (e ⇒ syn) (e' ⇒ syn') -> 
    =▷ syn syn' 
  vars-syn?-beyond {BHole} refl = =▷Refl
  vars-syn?-beyond {BVar x} vars-syn = vars-syn-beyond vars-syn

  data CtxInv : Var -> Type -> Ctx -> Ctx -> Set where 
    CtxInvInit : ∀ {Γ x t} ->
      CtxInv x t Γ (x ∶ t , Old ∷ Γ)
    CtxInvInit2 : ∀ {Γ x t} ->
      CtxInv x t (x ∶ t , New ∷ Γ) (x ∶ t , Old ∷ Γ)
    CtxInvNeq : ∀ {x x' t t' Γ Γ'} ->
      ¬(x ≡ x') ->
      CtxInv x t Γ Γ' ->
      CtxInv x t (x' ∶ t' ∷ Γ) (x' ∶ t' ∷ Γ')

  CtxInvNeq? : ∀ {x' x t t' Γ Γ'} ->
    ¬(BVar x ≡ x') ->
    CtxInv x t Γ Γ' ->
    CtxInv x t (x' ∶ t' ∷? Γ) (x' ∶ t' ∷? Γ')
  CtxInvNeq? {BHole} neq inv = inv
  CtxInvNeq? {BVar x} neq inv = CtxInvNeq (λ eq → neq (cong BVar eq)) inv

  ctx-inv-access-eq : ∀ {x t Γ Γ'} ->
    CtxInv x t Γ Γ' ->
    x , (t , Old) ∈N Γ' , ✔
  ctx-inv-access-eq CtxInvInit = InCtxFound
  ctx-inv-access-eq CtxInvInit2 = InCtxFound
  ctx-inv-access-eq (CtxInvNeq neq inv) = InCtxSkip neq (ctx-inv-access-eq inv)

  ctx-inv-access-neq : ∀ {x x' t t' m Γ Γ'} ->
    CtxInv x t Γ Γ' ->
    ¬ x' ≡ x ->
    x' , t' ∈N Γ , m ->
    x' , t' ∈N Γ' , m
  ctx-inv-access-neq CtxInvInit neq in-ctx = InCtxSkip neq in-ctx
  ctx-inv-access-neq CtxInvInit2 neq InCtxFound = ⊥-elim (neq refl)
  ctx-inv-access-neq CtxInvInit2 neq (InCtxSkip x in-ctx) = InCtxSkip neq in-ctx
  ctx-inv-access-neq (CtxInvNeq x inv) neq InCtxFound = InCtxFound
  ctx-inv-access-neq (CtxInvNeq x₁ inv) neq (InCtxSkip x in-ctx) = InCtxSkip x (ctx-inv-access-neq inv neq in-ctx)

  
  data UnwrapInv : Var -> Type -> Mark -> Ctx -> Ctx -> Set where 
    UnwrapInvInit : ∀ {Γ x n t t' m} ->
      (x , (t , n) ∈N Γ , m) -> 
      UnwrapInv x t m (x ∶ t' ∷ Γ) Γ
    UnwrapInvCons : ∀ {Γ Γ' x x' t t' m} ->
      ¬(x ≡ x') ->
      UnwrapInv x t m Γ Γ' -> 
      UnwrapInv x t m (x' ∶ t' ∷ Γ) (x' ∶ t' ∷ Γ') 

  UnwrapInvCons? : ∀ {x' Γ Γ' x t t' m} ->
    ¬(BVar x ≡ x') ->
    UnwrapInv x t m Γ Γ' -> 
    UnwrapInv x t m (x' ∶ t' ∷? Γ) (x' ∶ t' ∷? Γ') 
  UnwrapInvCons? {BHole} neq inv = inv
  UnwrapInvCons? {BVar x} neq inv = UnwrapInvCons (λ eq → neq (cong BVar eq)) inv

  unwrap-inv-access-eq : ∀ {x t m Γ Γ'} ->
    UnwrapInv x t m Γ Γ' ->
    ∃[ n ] (x , (t , n) ∈N Γ' , m)
  unwrap-inv-access-eq (UnwrapInvInit in-ctx) = _ , in-ctx
  unwrap-inv-access-eq (UnwrapInvCons x inv) = _ , InCtxSkip x (proj₂ (unwrap-inv-access-eq inv))

  
  unwrap-inv-access-neq : ∀ {x x' t t' m m' Γ Γ'} ->
    UnwrapInv x t m Γ Γ' ->
    ¬ (x ≡ x') ->
    x' , t' ∈N Γ , m' ->
    x' , t' ∈N Γ' , m'
  unwrap-inv-access-neq (UnwrapInvInit x) neq InCtxFound = ⊥-elim (neq refl)
  unwrap-inv-access-neq (UnwrapInvInit x) neq (InCtxSkip x₁ in-ctx) = in-ctx
  unwrap-inv-access-neq (UnwrapInvCons x inv) neq InCtxFound = InCtxFound
  unwrap-inv-access-neq (UnwrapInvCons x inv) neq (InCtxSkip neq' in-ctx) = InCtxSkip neq' (unwrap-inv-access-neq inv neq in-ctx)

  data CtxEquiv : Ctx -> Ctx -> Set where 
    CtxEquivInit : ∀ {x t t' Γ Γ'} ->
      CtxInv x t Γ Γ' ->
      CtxEquiv (x ∶ t' ∷ Γ) (x ∶ t' ∷ Γ') 
    CtxEquivUnwrapInit : ∀ {x t t' m Γ Γ'} ->
      UnwrapInv x t m Γ Γ' ->
      CtxEquiv (x ∶ t' ∷ Γ) (x ∶ t' ∷ Γ') 
    CtxEquivCons : ∀ {x t Γ Γ'} ->
      CtxEquiv Γ Γ' ->
      CtxEquiv (x ∶ t ∷ Γ) (x ∶ t ∷ Γ') 
  
  CtxEquivCons? : ∀ {x t Γ Γ'} ->
    CtxEquiv Γ Γ' ->
    CtxEquiv (x ∶ t ∷? Γ) (x ∶ t ∷? Γ') 
  CtxEquivCons? {BHole} equiv = equiv
  CtxEquivCons? {BVar x} equiv = CtxEquivCons equiv

  ctx-equiv-access : ∀ {x t Γ Γ' m} ->
    CtxEquiv Γ Γ' ->
    x , t ∈N Γ , m  ->
    x , t ∈N Γ' , m
  ctx-equiv-access (CtxEquivInit x) InCtxFound = InCtxFound
  ctx-equiv-access (CtxEquivInit x) (InCtxSkip x₁ in-ctx) = InCtxSkip x₁ (ctx-inv-access-neq x x₁ in-ctx)
  ctx-equiv-access (CtxEquivUnwrapInit x) InCtxFound = InCtxFound
  ctx-equiv-access (CtxEquivUnwrapInit x) (InCtxSkip x₁ in-ctx) = InCtxSkip x₁ (unwrap-inv-access-neq x (λ eq → x₁ (sym eq)) in-ctx)
  ctx-equiv-access (CtxEquivCons equiv) InCtxFound = InCtxFound
  ctx-equiv-access (CtxEquivCons equiv) (InCtxSkip x in-ctx) = InCtxSkip x (ctx-equiv-access equiv in-ctx)

  mutual 

    ctx-inv-ana : ∀ {Γ Γ' e} ->
      CtxEquiv Γ Γ' ->
      Γ L⊢ e ->
      Γ' L⊢ e
    ctx-inv-ana equiv (AnaSubsume x x₁ x₂ x₃) = AnaSubsume x x₁ x₂ (ctx-inv-syn equiv x₃)
    ctx-inv-ana equiv (AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ (ctx-inv-ana (CtxEquivCons? equiv) ana)

    ctx-inv-syn : ∀ {Γ Γ' e} ->
      CtxEquiv Γ Γ' ->
      Γ U⊢ e ->
      Γ' U⊢ e
    ctx-inv-syn equiv (SynConst x) = SynConst x
    ctx-inv-syn equiv (SynHole x) = SynHole x
    ctx-inv-syn equiv (SynAp x x₁ x₂ x₃ x₄ x₅) = SynAp x x₁ x₂ x₃ (ctx-inv-ana equiv x₄) (ctx-inv-ana equiv x₅)
    ctx-inv-syn equiv (SynVar x x₁) = SynVar (ctx-equiv-access equiv x) x₁
    ctx-inv-syn equiv (SynAsc x x₁ x₂) = SynAsc x x₁ (ctx-inv-ana equiv x₂)

  data NewCtxInv : Ctx -> Ctx -> Set where 
    NewCtxInvSame : ∀ {Γ} ->
      NewCtxInv Γ Γ
    NewCtxInvNew : ∀ {Γ x t} ->
      NewCtxInv Γ (x ∶ t , New ∷ Γ)
    NewCtxInvCons : ∀ {Γ Γ' x t} ->
      NewCtxInv Γ Γ' -> 
      NewCtxInv (x ∶ t ∷ Γ) (x ∶ t ∷ Γ') 
  
  NewCtxInvInit : ∀ {x Γ t} ->
    NewCtxInv Γ (x ∶ t , New ∷? Γ)
  NewCtxInvInit {BHole} = NewCtxInvSame
  NewCtxInvInit {BVar x} = NewCtxInvNew

  NewCtxInvCons? : ∀ {x Γ Γ' t} ->
    NewCtxInv Γ Γ' -> 
    NewCtxInv (x ∶ t ∷? Γ) (x ∶ t ∷? Γ') 
  NewCtxInvCons? {BHole} inv = inv
  NewCtxInvCons? {BVar x} inv = NewCtxInvCons inv

  new-ctx-beyond : ∀ {x t t' Γ Γ' m m'} ->
    NewCtxInv Γ Γ' ->
    (x , t ∈N Γ , m) ->
    (x , t' ∈N Γ' , m') ->
    (=▷ t t')
  new-ctx-beyond  NewCtxInvSame in-ctx in-ctx' with ∈N-unicity in-ctx in-ctx' 
  ... | refl , refl = =▷Refl
  new-ctx-beyond NewCtxInvNew in-ctx InCtxFound = =▷New
  new-ctx-beyond NewCtxInvNew in-ctx (InCtxSkip x in-ctx') = new-ctx-beyond NewCtxInvSame in-ctx in-ctx'
  new-ctx-beyond (NewCtxInvCons inv) InCtxFound InCtxFound = =▷Refl
  new-ctx-beyond (NewCtxInvCons inv) InCtxFound (InCtxSkip neq in-ctx') = ⊥-elim (neq refl)
  new-ctx-beyond (NewCtxInvCons inv) (InCtxSkip neq in-ctx) InCtxFound = ⊥-elim (neq refl)
  new-ctx-beyond (NewCtxInvCons inv) (InCtxSkip x in-ctx) (InCtxSkip x₁ in-ctx') = new-ctx-beyond inv in-ctx in-ctx'
 
  -- mutual 

  --   new-ctx-inv-ana : ∀ {Γ Γ' e} ->
  --     NewCtxInv Γ Γ' ->
  --     Γ ⊢ e ⇐ ->
  --     Γ' ⊢ e ⇐
  --   new-ctx-inv-ana inv (AnaSubsume x x₁ x₂ x₃) = AnaSubsume x x₁ x₂ (new-ctx-inv-syn inv x₃)
  --   new-ctx-inv-ana inv (AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = AnaFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ (new-ctx-inv-ana (NewCtxInvCons? inv) ana)

  --   new-ctx-inv-syn : ∀ {Γ Γ' e} ->
  --     NewCtxInv Γ Γ' ->
  --     Γ ⊢ e ⇒ ->
  --     Γ' ⊢ e ⇒
  --   new-ctx-inv-syn inv (SynConst x) = SynConst x
  --   new-ctx-inv-syn inv (SynHole x) = SynHole x
  --   new-ctx-inv-syn inv (SynAp x x₁ x₂ x₃ x₄ x₅) = SynAp x x₁ x₂ x₃ (new-ctx-inv-ana inv x₄) (new-ctx-inv-ana inv x₅)
  --   new-ctx-inv-syn inv (SynVar x x₁) = SynVar {!   !} {!   !}
  --   new-ctx-inv-syn inv (SynAsc x x₁ x₂) = SynAsc x x₁ (new-ctx-inv-ana inv x₂)


  mutual 

    preservation-vars-ana :
      ∀ {Γ Γ' x t m' e e' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      VarsSynthesize x t ✔ e e' ->
      CtxInv x t Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-vars-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (AnaSubsume subsumable consist-t consist-m syn) vars-syn ctx-inv with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = AnaSubsume (vars-syn-subsumable vars-syn subsumable) consist-t' (beyond-▶ (beyond-through-~N (vars-syn-beyond vars-syn) consist-t consist-t') consist-m) (preservation-vars-syn syn vars-syn ctx-inv)
    preservation-vars-ana (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunNeq {e-body' = e-body' ⇒ syn-body'} neq vars-syn) ctx-inv = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (vars-syn?-beyond vars-syn) consist-syn) consist-all consist-m-all (preservation-vars-ana ana vars-syn (CtxInvNeq? neq ctx-inv))    
    preservation-vars-ana (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunEq) ctx-inv = AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all (ctx-inv-ana (CtxEquivInit ctx-inv) ana)

    preservation-vars-syn :
      ∀ {Γ Γ' x t e e'} ->
      Γ U⊢ e ->
      VarsSynthesize x t ✔ e e' ->
      CtxInv x t Γ Γ' ->
      Γ' U⊢ e'
    preservation-vars-syn (SynConst consist) VSConst ctx-inv = SynConst consist
    preservation-vars-syn (SynHole consist) VSHole ctx-inv = SynHole consist
    preservation-vars-syn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} vars-syn-fun vars-syn-arg) ctx-inv with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (vars-syn-beyond vars-syn-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-ana syn vars-syn-fun ctx-inv) (preservation-vars-ana ana vars-syn-arg ctx-inv)
    preservation-vars-syn {t = t} (SynVar in-ctx consist) VSVarEq ctx-inv = SynVar (ctx-inv-access-eq ctx-inv) (▷Pair ▶Old) 
    preservation-vars-syn (SynVar in-ctx consist) (VSVarNeq neq) ctx-inv = SynVar (ctx-inv-access-neq ctx-inv (λ eq → neq (sym eq)) in-ctx) consist
    preservation-vars-syn (SynAsc consist-syn consist-ana ana) (VSAsc vars-syn) ctx-inv = SynAsc consist-syn consist-ana (preservation-vars-ana ana vars-syn ctx-inv)

  preservation-vars-ana? :
    ∀ {x Γ t e e' m' ana} ->
    (x ∶ t , New ∷? Γ) L⊢ (e [ m' ]⇐ ana) ->
    VarsSynthesize? x t ✔ e e' ->
    (x ∶ t , Old ∷? Γ) L⊢ (e' [ m' ]⇐ ana)
  preservation-vars-ana? {BHole} ana refl = ana
  preservation-vars-ana? {BVar x} ana vars-syn = preservation-vars-ana ana vars-syn CtxInvInit2

  preservation-vars-ana?-alt :
    ∀ {x Γ t e e' m' ana} ->
    Γ L⊢ (e [ m' ]⇐ ana) ->
    VarsSynthesize? x t ✔ e e' ->
    (x ∶ t , Old ∷? Γ) L⊢ (e' [ m' ]⇐ ana)
  preservation-vars-ana?-alt {BHole} ana refl = ana
  preservation-vars-ana?-alt {BVar x} ana vars-syn = preservation-vars-ana ana vars-syn CtxInvInit

  mutual 

    preservation-vars-unwrap-ana :
      ∀ {Γ Γ' x t m m' e e' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      VarsSynthesize x t m e e' ->
      UnwrapInv x t m Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-vars-unwrap-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (AnaSubsume subsumable consist-t consist-m syn) vars-syn ctx-inv with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = AnaSubsume (vars-syn-subsumable vars-syn subsumable) consist-t' (beyond-▶ (beyond-through-~N (vars-syn-beyond vars-syn) consist-t consist-t') consist-m) (preservation-vars-unwrap-syn syn vars-syn ctx-inv)
    preservation-vars-unwrap-ana (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunNeq {e-body' = e-body' ⇒ syn-body'} neq vars-syn) ctx-inv = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (vars-syn?-beyond vars-syn) consist-syn) consist-all consist-m-all (preservation-vars-unwrap-ana ana vars-syn (UnwrapInvCons? neq ctx-inv))    
    preservation-vars-unwrap-ana (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunEq) ctx-inv = AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all (ctx-inv-ana (CtxEquivUnwrapInit ctx-inv) ana)

    preservation-vars-unwrap-syn :
      ∀ {Γ Γ' x t m e e'} ->
      Γ U⊢ e ->
      VarsSynthesize x t m e e' ->
      UnwrapInv x t m Γ Γ' ->
      Γ' U⊢ e'
    preservation-vars-unwrap-syn (SynConst consist) VSConst ctx-inv = SynConst consist
    preservation-vars-unwrap-syn (SynHole consist) VSHole ctx-inv = SynHole consist
    preservation-vars-unwrap-syn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} vars-syn-fun vars-syn-arg) ctx-inv with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (vars-syn-beyond vars-syn-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-unwrap-ana syn vars-syn-fun ctx-inv) (preservation-vars-unwrap-ana ana vars-syn-arg ctx-inv)
    preservation-vars-unwrap-syn {t = t} (SynVar in-ctx consist) VSVarEq ctx-inv = SynVar (proj₂ (unwrap-inv-access-eq ctx-inv)) (▷Pair ▶Same)
    preservation-vars-unwrap-syn (SynVar in-ctx consist) (VSVarNeq neq) ctx-inv = SynVar (unwrap-inv-access-neq ctx-inv neq in-ctx) consist
    preservation-vars-unwrap-syn (SynAsc consist-syn consist-ana ana) (VSAsc vars-syn) ctx-inv = SynAsc consist-syn consist-ana (preservation-vars-unwrap-ana ana vars-syn ctx-inv)


  preservation-vars-unwrap : 
    ∀ {x Γ t t-old e e' m m' ana n} ->
    (x , (t , n) ∈N? Γ , m) -> 
    (x ∶ t-old ∷? Γ) L⊢ (e [ m' ]⇐ ana) ->
    VarsSynthesize? x t m e e' ->
    Γ L⊢ (e' [ m' ]⇐ ana)
  preservation-vars-unwrap {BHole} in-ctx ana refl = ana
  preservation-vars-unwrap {BVar x} in-ctx ana vars-syn = preservation-vars-unwrap-ana ana vars-syn (UnwrapInvInit in-ctx)
  