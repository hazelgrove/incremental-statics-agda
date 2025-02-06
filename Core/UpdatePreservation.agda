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
open import Core.WellTyped
open import Core.Update

module Core.UpdatePreservation where

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
  
  -- stays the same, except possibly becomes old
  data ◁= {A : Set} : NEW A -> NEW A -> Set where 
    ◁=Old : ∀ {t n} -> 
      ◁= (t , n) (t , Old)
    ◁=Refl : ∀ {t} -> ◁= t t

  max-new : (n : Newness) -> n ⊓ New ≡ New 
  max-new Old = refl
  max-new New = refl

  max-old : (n : Newness) -> n ⊓ Old ≡ n 
  max-old Old = refl
  max-old New = refl

  ~D-unless : ∀ {t1 t2} ->
    DUnless t1 t2 ~D t2 , ✔
  ~D-unless {t2 = □} = ~DVoidR
  ~D-unless {t2 = ■ x} = ~DVoidL 
  
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

  ▸TArrow-unicity : ∀ {t t-in t-in' t-out t-out' m m'} ->
    t ▸TArrow t-in , t-out , m -> 
    t ▸TArrow t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸TArrow-unicity MArrowBase MArrowBase = refl , refl , refl
  ▸TArrow-unicity MArrowHole MArrowHole = refl , refl , refl
  ▸TArrow-unicity MArrowArrow MArrowArrow = refl , refl , refl

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
  
  ~-unicity : ∀ {syn ana m m'} ->
    syn ~ ana , m -> 
    syn ~ ana , m' ->
    m ≡ m'
  ~-unicity ConsistBase ConsistBase = refl
  ~-unicity ConsistHoleL ConsistHoleL = refl
  ~-unicity ConsistHoleL ConsistHoleR = refl
  ~-unicity ConsistHoleR ConsistHoleL = refl
  ~-unicity ConsistHoleR ConsistHoleR = refl
  ~-unicity InconsistBaseArr InconsistBaseArr = refl
  ~-unicity InconsistArrBase InconsistArrBase = refl
  ~-unicity (ConsistArr con1 con2) (ConsistArr con3 con4) 
    rewrite ~-unicity con1 con3 
    rewrite ~-unicity con2 con4 = refl

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
  ∈N-unicity (InCtxSkip in-ctx) (InCtxSkip in-ctx') = ∈N-unicity in-ctx in-ctx'

  beyond-▸NTArrow : ∀ {syn syn' t-in t-in' t-out t-out' m m'} ->
    =▷ syn syn' ->
    syn ▸NTArrow t-in , t-out , m -> 
    syn' ▸NTArrow t-in' , t-out' , m' -> 
    (=▷ t-in t-in' × =▷ t-out t-out' × =▷ m m')
  beyond-▸NTArrow =▷New (NTArrowC _) (NTArrowC _) = =▷New , =▷New , =▷New
  beyond-▸NTArrow =▷Refl (NTArrowC match1) (NTArrowC match2) with ▸DTArrow-unicity match1 match2 
  ... | refl , refl , refl = =▷Refl , =▷Refl , =▷Refl

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
  preservation-lambda-lemma-3 {t = t , n} =▷New (▷Pair x) rewrite max-new n = ▷Pair ▶New
  preservation-lambda-lemma-3 =▷Refl consist = consist

  vars-syn-subsumable : ∀ {x t e e' syn syn'} ->
    VarsSynthesize x t (e ⇒ syn) (e' ⇒ syn') -> 
    SubsumableMid e ->
    SubsumableMid e'
  vars-syn-subsumable VSConst SubsumableConst = SubsumableConst
  vars-syn-subsumable VSHole SubsumableHole = SubsumableHole
  vars-syn-subsumable (VSFun vars-syn) ()
  vars-syn-subsumable (VSAp vars-syn1 vars-syn2) SubsumableAp = SubsumableAp
  vars-syn-subsumable VSVar SubsumableVar = SubsumableVar
  vars-syn-subsumable (VSOtherVar _) SubsumableVar = SubsumableVar
  vars-syn-subsumable (VSAsc vars-syn) SubsumableAsc = SubsumableAsc

  vars-syn-beyond : ∀ {x t e syn e' syn'} ->
    VarsSynthesize x t (e ⇒ syn) (e' ⇒ syn') -> 
    =▷ syn syn' 
  vars-syn-beyond VSConst = =▷Refl
  vars-syn-beyond VSHole = =▷Refl
  vars-syn-beyond (VSFun syn) = =▷Refl
  vars-syn-beyond (VSAp syn syn₁) = =▷Refl
  vars-syn-beyond VSVar = =▷New
  vars-syn-beyond (VSOtherVar x) = =▷Refl
  vars-syn-beyond (VSAsc syn) = =▷Refl

  -- -- this is imprecise : the =▷D relation is bigger than required. oh well. 
  beyond-U↦ : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') -> 
    =▷ syn syn' 
  beyond-U↦ (StepAp _) = =▷New
  beyond-U↦ StepAsc = =▷New

  beyond-U↦-env : ∀ {ε e e' e-in e-in' syn syn'} -> 
    e-in U↦ e-in' -> 
    ε U⟦ e-in ⟧Up== (e ⇒ syn) ->
    ε U⟦ e-in' ⟧Up== (e' ⇒ syn') ->
    =▷ syn syn' 
  beyond-U↦-env step FillU⊙ FillU⊙ = beyond-U↦ step
  beyond-U↦-env step (FillUEnvUpRec _) (FillUEnvUpRec _) = =▷Refl

  beyond-▷-contra : 
    {A : Set} -> 
    {a b b' : NEW A} ->
    ◁= b b' ->
    ▷ a b ->
    ▷ a b' 
  beyond-▷-contra ◁=Old (▷Pair consist) = ▷Pair consist
  beyond-▷-contra ◁=Refl consist = consist

  beyond-▷■-contra : 
    {A : Set} -> 
    {a : NEW A} ->
    {b b' : NEW (DATA A)} ->
    ◁= b b' ->
    ▷■ a b ->
    ▷■ a b' 
  beyond-▷■-contra ◁=Old (▷■Pair (▷Pair consist)) = ▷■Pair (▷Pair consist)
  beyond-▷■-contra ◁=Refl consist = consist

  beyond-L↦ : ∀ {e e' m m' ana ana'} -> 
    (e [ m ]⇐ ana) L↦ (e' [ m' ]⇐ ana') -> 
    ◁= ana ana' 
  beyond-L↦ (StepNewSynConsist _) = ◁=Refl
  beyond-L↦ (StepNewAnaConsist _ _) = ◁=Old
  beyond-L↦ (StepAnaFun _ _) = ◁=Old
  beyond-L↦ (StepSynFun) = ◁=Old
  beyond-L↦ (StepNewAnnFun _) = ◁=Refl

  beyond-L↦-inner : ∀ {e e' syn syn'} -> 
    ((e ⇒ syn) [ ✔ ]⇐ (□ , Old)) L↦ ((e' ⇒ syn') [ ✔ ]⇐ (□ , Old)) -> 
    =▷ syn syn' 
  beyond-L↦-inner (StepNewAnnFun x) = =▷New
  beyond-L↦-inner StepSynFun = =▷New

  beyond-L↦-env : ∀ {ε e e' e-in e-in' m m' ana ana'} -> 
    e L↦ e' -> 
    ε L⟦ e ⟧Low== (e-in [ m ]⇐ ana) ->
    ε L⟦ e' ⟧Low== (e-in' [ m' ]⇐ ana') ->
    ◁= ana ana' 
  beyond-L↦-env step FillL⊙ FillL⊙ = beyond-L↦ step
  beyond-L↦-env step (FillLEnvLowRec _) (FillLEnvLowRec _) = ◁=Refl

  step-subsumable : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') ->
    SubsumableMid e -> 
    SubsumableMid e'
  step-subsumable (StepAp _) SubsumableAp = SubsumableAp
  step-subsumable StepAsc SubsumableAsc = SubsumableAsc

  step-l-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    e-in L↦ e-in' -> 
    ε L⟦ e-in ⟧Mid== e ->
    ε L⟦ e-in' ⟧Mid== e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  step-l-env-subsumable step (FillLEnvFun _) (FillLEnvFun _) ()
  step-l-env-subsumable step (FillLEnvAp1 _) (FillLEnvAp1 _) SubsumableAp = SubsumableAp
  step-l-env-subsumable step (FillLEnvAp2 _) (FillLEnvAp2 _) SubsumableAp = SubsumableAp
  step-l-env-subsumable step (FillLEnvAsc _) (FillLEnvAsc _) SubsumableAsc = SubsumableAsc

  step-u-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    e-in U↦ e-in' -> 
    ε U⟦ e-in ⟧Mid== e ->
    ε U⟦ e-in' ⟧Mid== e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  step-u-env-subsumable step (FillUEnvFun _) (FillUEnvFun _) ()
  step-u-env-subsumable step (FillUEnvAp1 _) (FillUEnvAp1 _) SubsumableAp = SubsumableAp
  step-u-env-subsumable step (FillUEnvAp2 _) (FillUEnvAp2 _) SubsumableAp = SubsumableAp
  step-u-env-subsumable step (FillUEnvAsc _) (FillUEnvAsc _) SubsumableAsc = SubsumableAsc

  -- oldify-▷D : ∀ {d t n} ->
  --   ▷D d (■ (t , n)) -> 
  --   ▷D d (■ (t , Old))
  -- oldify-▷D ▷DVoidL = ▷DVoidL
  -- oldify-▷D (▷DSome MergeInfoNew) = ▷DSome MergeInfoNew
  -- oldify-▷D (▷DSome (MergeInfoOld refl)) = ▷DSome (MergeInfoOld refl)

  oldify-syn : ∀ {Γ e t n} ->
    Γ ⊢ e ⇒ (t , n) ⇒ ->
    Γ ⊢ e ⇒ (t , Old) ⇒
  oldify-syn (SynConst (▷Pair consist)) = SynConst (▷Pair consist) 
  oldify-syn (SynHole (▷Pair consist)) = SynHole (▷Pair consist)
  oldify-syn (SynAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana) = SynAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana
  oldify-syn (SynVar in-ctx (▷■Pair (▷Pair consist))) = SynVar in-ctx (▷■Pair (▷Pair consist)) 
  oldify-syn (SynAsc (▷■Pair (▷Pair consist-syn)) consist-ana ana) = SynAsc (▷■Pair (▷Pair consist-syn)) consist-ana ana
  
  oldify-syn-inner : ∀ {Γ e t n} ->
    Γ ⊢ ((e ⇒ (t , n)) [ ✔ ]⇐ (□ , Old)) ⇐ ->
    Γ ⊢ ((e ⇒ (t , Old)) [ ✔ ]⇐ (□ , Old)) ⇐
  oldify-syn-inner (AnaSubsume subsumable _ _ syn) = AnaSubsume subsumable (~N-pair ~DVoidR) ▶Old (oldify-syn syn) 
  oldify-syn-inner (AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ x₅ x₆ x₇ syn) = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ (beyond-▷-contra ◁=Old x₅) (~N-pair ~DVoidR) ▶Old syn

  newify-ana : ∀ {Γ e m ana t} ->
    Γ ⊢ e [ m ]⇐ ana ⇐ -> 
    Γ ⊢ e [ m ]⇐ (t , New) ⇐
  newify-ana {t = t} (AnaSubsume {syn-all = syn-all} subsumable consist-t consist-m syn) with ~N-dec syn-all ((t , New)) 
  ... | _ , consist-t' with new-through-~N-left consist-t' 
  ... | _ , refl = AnaSubsume subsumable consist-t' ▶New syn
  newify-ana {t = t-ana'} (AnaFun {syn-all = syn-all} {syn-body = syn-body , n-body} {t-asc = t-asc , n-asc} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ▸DTArrow-dec t-ana' | ~N-dec syn-all (t-ana' , New )
  ... | t-in-ana' , t-out-ana' , m-ana-ana' , marrow' | _ , consist-syn' with ~D-dec (■ t-asc) t-in-ana' | new-through-~N-left consist-syn' 
  ... | _ , consist' | _ , refl rewrite max-new (n-asc ⊓ n-body) = AnaFun (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▷Pair ▶New) ▶New ▶New-max-r consist-helper consist-syn' ▶New ana 
    where 
    consist-helper : ∀ {t} -> ▷ (t , ((n-asc ⊓ n-body) ⊓ New)) syn-all 
    consist-helper rewrite max-new (n-asc ⊓ n-body) = ▷Pair ▶New


  oldify-ctx : Ctx -> ℕ -> Ctx 
  oldify-ctx ∅ x = ∅
  oldify-ctx ((t , n) ∷ Γ) zero = ((t , Old) ∷ Γ)
  oldify-ctx ((t , n) ∷ Γ) (suc x) = ((t , n) ∷ (oldify-ctx Γ x))

  oldify-access : ∀ {x t n Γ m} ->
    x , (t , n) ∈N Γ , m ->
    x , (t , Old) ∈N oldify-ctx Γ x , m
  oldify-access InCtxEmpty = InCtxEmpty
  oldify-access InCtxFound = InCtxFound
  oldify-access (InCtxSkip in-ctx) = InCtxSkip (oldify-access in-ctx)

  oldify-access-neq : ∀ {x y t Γ m} ->
    y , t ∈N Γ , m ->
    ¬(y ≡ x) ->
    y , t ∈N oldify-ctx Γ x , m
  oldify-access-neq InCtxEmpty neq = InCtxEmpty
  oldify-access-neq {x = zero} InCtxFound neq = ⊥-elim (neq refl)
  oldify-access-neq {x = suc x} InCtxFound neq = InCtxFound
  oldify-access-neq {x = zero} (InCtxSkip in-ctx) neq = InCtxSkip in-ctx
  oldify-access-neq {x = suc x} (InCtxSkip in-ctx) neq = InCtxSkip (oldify-access-neq in-ctx λ eq → neq (cong suc eq))
  
  mutual 

    preservation-vars-ana :
      ∀ {Γ Γ' x t e e' m ana} ->
      (Γ ⊢ (e [ m ]⇐ ana) ⇐) ->
      VarsSynthesize x t e e' ->
      x , (t , New) ∈N Γ , ✔ ->
      oldify-ctx Γ x ≡ Γ' ->
      (Γ' ⊢ (e' [ m ]⇐ ana) ⇐)
    preservation-vars-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (AnaSubsume subsumable consist-t consist-m syn) vars-syn in-ctx refl with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = AnaSubsume (vars-syn-subsumable vars-syn subsumable) consist-t' (beyond-▶ (beyond-through-~N (vars-syn-beyond vars-syn) consist-t consist-t') consist-m) (preservation-vars-syn syn vars-syn in-ctx refl)
    preservation-vars-ana (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFun {e-body' = e-body' ⇒ syn-body'} vars-syn) in-ctx refl 
      = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (vars-syn-beyond vars-syn) consist-syn) consist-all consist-m-all (preservation-vars-ana ana vars-syn (InCtxSkip in-ctx) refl)      

    preservation-vars-syn :
      ∀ {Γ Γ' x t e e'} ->
      (Γ ⊢ e ⇒) ->
      VarsSynthesize x t e e' ->
      x , (t , New) ∈N Γ , ✔ ->
      oldify-ctx Γ x ≡ Γ' ->
      (Γ' ⊢ e' ⇒)
    -- preservation-vars-syn = {!   !}
    preservation-vars-syn (SynConst consist) VSConst in-ctx refl = SynConst consist
    preservation-vars-syn (SynHole consist) VSHole in-ctx refl = SynHole consist
    -- preservation-vars-syn (SynFun consist syn) (VSFun {e-body' = e-body' ⇒ syn-body'} vars-syn) in-ctx refl = SynFun (preservation-lambda-lemma (vars-syn-beyond vars-syn) consist) (preservation-vars-syn syn vars-syn (InCtxSkip in-ctx) refl)
    preservation-vars-syn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} vars-syn-fun vars-syn-arg) in-ctx refl with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (vars-syn-beyond vars-syn-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-ana syn vars-syn-fun in-ctx refl) (preservation-vars-ana ana vars-syn-arg in-ctx refl)
    preservation-vars-syn {t = t} (SynVar in-ctx consist) VSVar in-ctx' refl with ∈N-unicity in-ctx in-ctx' 
    ... | refl , refl = SynVar (oldify-access in-ctx) (▷■Pair (▷Pair ▶Old)) 
    preservation-vars-syn (SynVar in-ctx consist) (VSOtherVar neq) in-ctx' refl = SynVar (oldify-access-neq in-ctx neq) consist
    preservation-vars-syn (SynAsc consist-syn consist-ana ana) (VSAsc vars-syn) in-ctx refl = SynAsc consist-syn consist-ana (preservation-vars-ana ana vars-syn in-ctx refl)

  -- preservation-vars-indirect-syn :
  --   ∀ {Γ Γ' x t e e' m} ->
  --   (Γ ⊢ (e [ m ]⇐ (□ , Old)) ⇐) ->
  --   VarsSynthesize x t e e' ->
  --   x , (t , New) ∈N Γ , ✔ ->
  --   oldify-ctx Γ x ≡ Γ' ->
  --   (Γ' ⊢ (e' [ m ]⇐ (□ , Old)) ⇐)
  -- preservation-vars-indirect-syn (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) vars-syn in-ctx refl = {!   !}
  -- preservation-vars-indirect-syn (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFun vars-syn) in-ctx refl = {!   !} 

  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇒) ->
    (e U↦ e') ->   
    (Γ ⊢ e' ⇒)
  PreservationStepSyn (SynConst _) ()
  PreservationStepSyn (SynHole _) ()
  PreservationStepSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepAp marrow') = SynAp (NTArrowC (DTArrowSome marrow')) (▷Pair ▶Old) (▷Pair ▶Old) ▶Old (oldify-syn-inner syn) (newify-ana ana)
  PreservationStepSyn (SynVar _ _) ()
  PreservationStepSyn (SynAsc consist-syn consist-ana ana) StepAsc = SynAsc (▷■Pair (▷Pair ▶Old)) (▷■Pair (▷Pair ▶Old)) (newify-ana ana)
  
  PreservationStepAna :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇐) ->
    (e L↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationStepAna (AnaSubsume subsumable (~N-pair consist-t) consist-m syn) (StepNewSynConsist consist) with consist-t 
  ... | ~DSome consist-t rewrite ~-unicity consist consist-t = AnaSubsume subsumable (~N-pair (~DSome consist-t)) ▶Old (oldify-syn syn)
  PreservationStepAna (AnaSubsume subsumable (~N-pair (~DSome consist-t)) consist-m syn) (StepNewAnaConsist subsumable' consist) rewrite ~-unicity consist consist-t = AnaSubsume subsumable' (~N-pair (~DSome consist-t)) ▶Old (oldify-syn syn)
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn (~N-pair (~DSome consist-all)) consist-m-all ana) (StepNewSynConsist consist') rewrite ~-unicity consist' consist-all  = AnaFun marrow consist consist-ana consist-asc consist-body (beyond-▷-contra ◁=Old consist-syn) (~N-pair (~DSome consist-all)) ▶Old ana
  PreservationStepAna (AnaFun (NTArrowC x) consist (▷Pair ▶New) ▶New consist-body consist-syn consist-all consist-m-all ana) (StepAnaFun marrow' (■~D-pair consist')) = AnaFun (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▷Pair ▶Old) ▶Old ▶Same (▷Pair ▶Same) (~N-pair ~D-unless) ▶Same (newify-ana ana)
  PreservationStepAna (AnaFun {e-body = e-body} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepNewAnnFun {e-body' = e-body' ⇒ (syn-body' , n-syn-body')} {t-asc} {t-body} {n-body} vars-syn) = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old ▶Old (preservation-lambda-lemma-2 (vars-syn-beyond vars-syn')) (~N-pair ~DVoidR) ▶New (preservation-vars-ana ana vars-syn InCtxFound refl)
    where 
    vars-syn' : VarsSynthesize 0 t-asc (e-body ⇒ (■ t-body , n-body)) (e-body' ⇒ (syn-body' , n-syn-body' ⊓ Old))
    vars-syn' rewrite max-old n-syn-body' = vars-syn
  -- snag : generalize oldify-syn-inner.
  PreservationStepAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) StepSynFun = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) (▷Pair ▶Old) ▶Old ▶Same (▷Pair ▶Same) (~N-pair ~DVoidR) ▶New {! oldify-syn-inner  !}
  
  -- PreservationStepSyn (SynFun consist syn) (StepNewAnnFun {e-body' = e-body' ⇒ syn-body'} vars-syn) = SynFun (preservation-lambda-lemma-2 (vars-syn-beyond vars-syn)) (preservation-vars-syn syn vars-syn InCtxFound refl)
  -- PreservationStepSyn (SynFun consist syn) (StepNewSynFun {t-asc = t-asc} {t-body} {n-asc}) = SynFun (direct-arrow-consist-lemma t-asc t-body n-asc Old) (oldify-syn syn)


  mutual 

    PreservationSyn :  
      ∀ {Γ e e'} ->
      (Γ ⊢ e ⇒) ->
      (e Up↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
    PreservationSyn (SynConst _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynConst _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynHole _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynHole _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))    
    PreservationSyn (SynVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynVar _ _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙)))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-U↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = (e-fun' ⇒ syn-fun') [ ✔ ]⇐ (□ , Old)} (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-L↦-inner step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepLow FillL⊙ step FillL⊙)) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) = SynAp marrow consist-syn (beyond-▷-contra (beyond-L↦-env step FillL⊙ FillL⊙) consist-ana) consist-mark syn (PreservationAna ana (StepLow FillL⊙ step FillL⊙))  
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) = SynAsc consist-syn (beyond-▷■-contra (beyond-L↦-env step fill1 fill2) consist-ana) (PreservationAna ana (StepLow fill1 step fill2))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec fill2)))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))

    PreservationAna :  
      ∀ {Γ e e'} -> 
      (Γ ⊢ e ⇐) ->
      (e Low↦ e') ->   
      (Γ ⊢ e' ⇐) 
    PreservationAna ana (StepLow FillL⊙ step FillL⊙) = PreservationStepAna ana step
    PreservationAna (AnaSubsume {ana-all = ana-all} subsumable consist-t consist-m syn) (StepUp {e-in' = e-all' ⇒ syn-all'} (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)) with ~N-dec syn-all' ana-all 
    ... | m' , consist-t' = AnaSubsume (step-subsumable step subsumable) consist-t' (beyond-▶ (beyond-through-~N (beyond-U↦ step) consist-t consist-t') consist-m) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))    
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))) = AnaSubsume (step-u-env-subsumable step fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))) = AnaSubsume (step-l-env-subsumable step fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2))) 
    PreservationAna (AnaFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma-3 {t = t-asc} (beyond-U↦-env step fill1 fill2) consist-syn) consist-all consist-m-all (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) 
    -- snag : this one's subtle.
    PreservationAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ syn') [ m' ]⇐ ana'} fill2)))) = AnaFun marrow consist (beyond-▷-contra (beyond-L↦-env step fill1 fill2) consist-ana) consist-asc consist-body {!   !} consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
  