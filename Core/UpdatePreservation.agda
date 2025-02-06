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

  -- mutual 

  --   UEnvUpCtx : Ctx -> UEnvUp -> Ctx 
  --   UEnvUpCtx Γ U⊙ = Γ
  --   UEnvUpCtx Γ (UEnvUpRec x ε) = UEnvMidCtx Γ ε

  --   UEnvMidCtx : Ctx -> UEnvMid -> Ctx
  --   UEnvMidCtx Γ (UEnvFun t x₁ ε) = UEnvLowCtx (t , Γ) ε
  --   UEnvMidCtx Γ (UEnvAp1 ε x₁ x₂) = UEnvLowCtx Γ ε
  --   UEnvMidCtx Γ (UEnvAp2 x x₁ ε) = UEnvLowCtx Γ ε
  --   UEnvMidCtx Γ (UEnvAsc x ε) = UEnvLowCtx Γ ε

  --   UEnvLowCtx : Ctx -> UEnvLow -> Ctx
  --   UEnvLowCtx Γ (UEnvLowRec x x₁ ε) = UEnvUpCtx Γ ε 

  -- LEnvUpCtx : Ctx -> LEnvUp -> Ctx
  -- LEnvUpCtx = {!   !}

  -- LEnvUpFillTyping : 
  --   ∀ {Γ ε e e' t e-in e-in' t-in } ->
  --   ((LEnvUpCtx Γ ε) ⊢ e-in ⇐ t-in) ->
  --   (ε L⟦ e-in ⟧Up== e) -> 
  --   (Γ ⊢ e ⇒ t) ->
  --   ((LEnvUpCtx Γ ε) ⊢ e-in' ⇐ t-in) ->
  --   (ε L⟦ e-in' ⟧Up== e') -> 
  --   (Γ ⊢ e' ⇒ t)
  -- LEnvUpFillTyping = {!   !}

  -- UEnvLowFillTyping : 
  --   ∀ {Γ ε e e' t e-in e-in' t-in } ->
  --   ((UEnvLowCtx Γ ε) ⊢ e-in ⇒ t-in) ->
  --   (ε U⟦ e-in ⟧Low== e) -> 
  --   (Γ ⊢ e ⇐ t) ->
  --   ((UEnvLowCtx Γ ε) ⊢ e-in' ⇒ t-in) ->
  --   (ε U⟦ e-in' ⟧Low== e') -> 
  --   (Γ ⊢ e' ⇐ t)
  -- UEnvLowFillTyping = {!   !}

  -- UEnvUpFillTyping : 
  --   ∀ {Γ ε e e' t e-in e-in' t-in } ->
  --   ((UEnvUpCtx Γ ε) ⊢ e-in ⇒ t-in) ->
  --   (ε U⟦ e-in ⟧Up== e) -> 
  --   (Γ ⊢ e ⇒ t) ->
  --   ((UEnvUpCtx Γ ε) ⊢ e-in' ⇒ t-in) ->
  --   (ε U⟦ e-in' ⟧Up== e') -> 
  --   (Γ ⊢ e' ⇒ t)
  -- UEnvUpFillTyping syn-in1 FillU⊙ syn syn-in2 FillU⊙ rewrite (syn-unicity syn syn-in1) = syn-in2
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1))) (SynFun syn mn m) syn-in2 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill2))) = SynFun (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2) mn m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1))) (SynFunVoid syn) syn-in2 (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill2))) = SynFunVoid (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2)
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) (SynAp syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))) = SynAp (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2) mt mn ana m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill1))) (SynApFail syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec fill2))) = SynApFail (UEnvUpFillTyping syn-in1 fill1 syn syn-in2 fill2) mt mn ana m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp2 fill1)) (SynAp syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp2 fill2)) = SynAp syn mt mn (UEnvLowFillTyping syn-in1 fill1 ana syn-in2 fill2) m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAp2 fill1)) (SynApFail syn mt mn ana m) syn-in2 (FillUEnvUpRec (FillUEnvAp2 fill2)) = SynApFail syn mt mn (UEnvLowFillTyping syn-in1 fill1 ana syn-in2 fill2) m
  -- UEnvUpFillTyping syn-in1 (FillUEnvUpRec (FillUEnvAsc fill1)) (SynAsc ana m) syn-in2 (FillUEnvUpRec (FillUEnvAsc fill2)) = SynAsc (UEnvLowFillTyping syn-in1 fill1 ana syn-in2 fill2) m

  -- merge-syn-consist : ∀ {t n syn syn'} ->
  --   MergeSyn (t , n) syn syn' ->
  --   (t , Old) ▷ syn'
  -- merge-syn-consist MergeSynVoid = MergeInfoOld
  -- merge-syn-consist (MergeSynMerge (MergeInfoType _)) = MergeInfoOld

  -- merge-ana-consist : ∀ {t n ana ana'} ->
  --   MergeAna (t , n) ana ana' ->
  --   (t , Old) ▷ ana'
  -- merge-ana-consist MergeAnaVoid = MergeInfoOld
  -- merge-ana-consist (MergeAnaMerge (MergeInfoType _)) = MergeInfoOld

  -- oldify-syn : ∀ {Γ t n e} ->
  --   Γ ⊢ EUp (⇑ (t , n)) e ⇒ ->
  --   Γ ⊢ EUp (⇑ (t , Old)) e ⇒
  -- oldify-syn (SynConst (SynConsistMerge MergeInfoOld)) = SynConst (SynConsistMerge MergeInfoOld)
  -- oldify-syn (SynHole (SynConsistMerge MergeInfoOld)) = SynHole (SynConsistMerge MergeInfoOld)

  -- freshen-ana : ∀ {Γ ana m e t n ana'} ->
  --   Γ ⊢ ELow ana m e ⇐ ->
  --   MergeAna (t , n) ana ana' ->
  --   Γ ⊢ ELow (⇓ ana') m e ⇐
  -- freshen-ana () merge

  -- oldify-ntmatch : ∀ {t n t1 t2 m n1 n2 n3} ->
  --   (t , n) ▸NTArrow (t1 , n1) , (t2 , n2) , (m , n3) ->
  --   (t , Old) ▸NTArrow (t1 , Old) , (t2 , Old) , (m , MarkOld)
  -- oldify-ntmatch (MNTArrowOldMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowOldNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch (MNTArrowNewMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowNewNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch MNTArrowArrow = MNTArrowOldMatch MArrowArrow

  -- data =▷M : NewMark -> NewMark -> Set where 
  --   =▷MNew : ∀ {s m} -> 
  --     =▷M s (m , New)
  --   ▷MRefl : ∀ {s} -> 
  --     =▷M s s

  -- data =▷T : NewType -> NewType -> Set where 
  --   =▷TNew : ∀ {s t} -> 
  --     =▷T s (t , New)
  --   =▷TRefl : ∀ {s} -> 
  --     =▷T s s

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

  new-max-r : (n : Newness) -> n ⊓ New ≡ New 
  new-max-r Old = refl
  new-max-r New = refl
  
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
  new-through-~N-left (~N-pair {n1 = n1} consist) rewrite new-max-r n1 = _ , refl

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
  ▶New-max-r {n = n} rewrite new-max-r n = ▶New

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
  preservation-lambda-lemma {t = t , n} =▷New (▷Pair consist) rewrite new-max-r n = ▷Pair ▶New
  preservation-lambda-lemma =▷Refl consist = consist

  -- direct-arrow-consist-lemma : 
  --   (t1 t2 : Type) -> 
  --   (n1 n2 : Newness) ->
  --   ▷D (■ (NTArrow (t1 , n1) (t2 , n2))) (■ (TArrow t1 t2 , New))
  -- direct-arrow-consist-lemma t1 t2 Old Old = ▷DSome (MergeInfoOld refl)
  -- direct-arrow-consist-lemma t1 t2 Old New = ▷DSome MergeInfoNew
  -- direct-arrow-consist-lemma t1 t2 New Old = ▷DSome MergeInfoNew
  -- direct-arrow-consist-lemma t1 t2 New New = ▷DSome MergeInfoNew

  -- preservation-lambda-lemma-2 : ∀ {t1 t2 n syn} ->
  --   =▷D (■ (t2 , n)) syn -> 
  --   ▷D (SynArrow (t1 , Old) syn) (■ (TArrow t1 t2 , New))
  -- preservation-lambda-lemma-2 =▷DNew = ▷DSome MergeInfoNew
  -- preservation-lambda-lemma-2 {t1} {t2} {n} =▷DRefl = direct-arrow-consist-lemma t1 t2 Old n

  -- vars-syn-subsumable : ∀ {x t e e' syn syn'} ->
  --   VarsSynthesize x t (e ⇒ syn) (e' ⇒ syn') -> 
  --   SubsumableMid e ->
  --   SubsumableMid e'
  -- vars-syn-subsumable VSConst SubsumableConst = SubsumableConst
  -- vars-syn-subsumable VSHole SubsumableHole = SubsumableHole
  -- vars-syn-subsumable (VSFun vars-syn) ()
  -- vars-syn-subsumable (VSAp vars-syn1 vars-syn2) SubsumableAp = SubsumableAp
  -- vars-syn-subsumable VSVar SubsumableVar = SubsumableVar
  -- vars-syn-subsumable (VSOtherVar _) SubsumableVar = SubsumableVar
  -- vars-syn-subsumable (VSAsc vars-syn) SubsumableAsc = SubsumableAsc

  -- vars-syn-beyond : ∀ {x t e syn e' syn'} ->
  --   VarsSynthesize x t (e ⇒ syn) (e' ⇒ syn') -> 
  --   =▷D syn syn' 
  -- vars-syn-beyond VSConst = =▷DRefl
  -- vars-syn-beyond VSHole = =▷DRefl
  -- vars-syn-beyond (VSFun syn) = =▷DRefl
  -- vars-syn-beyond (VSAp syn syn₁) = =▷DRefl
  -- vars-syn-beyond VSVar = =▷DNew
  -- vars-syn-beyond (VSOtherVar x) = =▷DRefl
  -- vars-syn-beyond (VSAsc syn) = =▷DRefl

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

  -- -- stays the same, except possibly becomes old
  -- data ◁=D : TypeData -> TypeData -> Set where 
  --   ◁=DOld : ∀ {t n} -> 
  --     ◁=D (■ (t , n)) (■ (t , Old))
  --   ◁=DRefl : ∀ {t} -> ◁=D t t


  -- beyond-consist-contra : ∀ {t ana ana'} ->
  --   ◁=D ana ana' ->
  --   ▷D (■ t) ana ->
  --   ▷D (■ t) ana'
  -- beyond-consist-contra ◁=DOld (▷DSome MergeInfoNew) = ▷DSome MergeInfoNew
  -- beyond-consist-contra ◁=DOld (▷DSome (MergeInfoOld refl)) = ▷DSome (MergeInfoOld refl)
  -- beyond-consist-contra ◁=DRefl consist = consist

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
    Γ ⊢ e [ m ]⇐ (■ t , New) ⇐
  newify-ana {t = t} (AnaSubsume {syn-all = syn-all} subsumable consist-t consist-m syn) with ~N-dec syn-all ((■ t , New)) 
  ... | _ , consist-t' with new-through-~N-left consist-t' 
  ... | _ , refl = AnaSubsume subsumable consist-t' ▶New syn
  newify-ana {t = t-ana'} (AnaFun {syn-all = syn-all} {t-asc = t-asc , n-asc} (NTArrowC marrow) ana consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all) with ▸TArrow-dec t-ana' | ~N-dec syn-all (■ t-ana' , New )
  ... | t-in-ana' , t-out-ana' , m-ana-ana' , marrow' | _ , consist-syn' with ~-dec t-asc t-in-ana' | new-through-~N-left consist-syn' 
  ... | _ , consist' | _ , refl = AnaFun (NTArrowC (DTArrowSome marrow')) (■~N-pair (~N-pair (~DSome consist'))) (▷Pair ▶New) ▶New ▶New-max-r consist-body consist-syn' ▶New consist-m-all

  -- oldify-ctx : Ctx -> ℕ -> Ctx 
  -- oldify-ctx ∅ x = ∅
  -- oldify-ctx ((t , n) ∷ Γ) zero = ((t , Old) ∷ Γ)
  -- oldify-ctx ((t , n) ∷ Γ) (suc x) = ((t , n) ∷ (oldify-ctx Γ x))

  -- oldify-access : ∀ {x t n Γ m} ->
  --   x , (t , n) ∈NM Γ , m ->
  --   x , (t , Old) ∈NM oldify-ctx Γ x , m
  -- oldify-access InCtxEmpty = InCtxEmpty
  -- oldify-access InCtxFound = InCtxFound
  -- oldify-access (InCtxSkip in-ctx) = InCtxSkip (oldify-access in-ctx)

  -- oldify-access-neq : ∀ {x y t Γ m} ->
  --   y , t ∈NM Γ , m ->
  --   ¬(y ≡ x) ->
  --   y , t ∈NM oldify-ctx Γ x , m
  -- oldify-access-neq InCtxEmpty neq = InCtxEmpty
  -- oldify-access-neq {x = zero} InCtxFound neq = ⊥-elim (neq refl)
  -- oldify-access-neq {x = suc x} InCtxFound neq = InCtxFound
  -- oldify-access-neq {x = zero} (InCtxSkip in-ctx) neq = InCtxSkip in-ctx
  -- oldify-access-neq {x = suc x} (InCtxSkip in-ctx) neq = InCtxSkip (oldify-access-neq in-ctx λ eq → neq (cong suc eq))
  
  -- mutual 

  --   PreservationVarsAna :
  --     ∀ {Γ Γ' x t e e' m ana} ->
  --     (Γ ⊢ (e [ m ]⇐ ana) ⇐) ->
  --     VarsSynthesize x t e e' ->
  --     x , (t , New) ∈NM Γ , ✔ ->
  --     oldify-ctx Γ x ≡ Γ' ->
  --     (Γ' ⊢ (e' [ m ]⇐ ana) ⇐)
  --   PreservationVarsAna {e' = e-all' ⇒ syn-all'} {ana = ana} (AnaSubsume subsumable consist-t consist-m syn) vars-syn in-ctx refl with ~D-dec syn-all' ana 
  --   ... | m-consist' , consist-t' = AnaSubsume (vars-syn-subsumable vars-syn subsumable) consist-t' (beyond-consist-m (beyond-through-~D (vars-syn-beyond vars-syn) consist-t consist-t') consist-m) (PreservationVarsSyn syn vars-syn in-ctx refl)
  --   PreservationVarsAna (AnaFun marrow ana consist consist-ana consist-asc consist-body edge) (VSFun vars-syn) in-ctx refl = AnaFun marrow (PreservationVarsAna ana vars-syn (InCtxSkip in-ctx) refl) consist consist-ana consist-asc consist-body edge

  --   PreservationVarsSyn :
  --     ∀ {Γ Γ' x t e e'} ->
  --     (Γ ⊢ e ⇒) ->
  --     VarsSynthesize x t e e' ->
  --     x , (t , New) ∈NM Γ , ✔ ->
  --     oldify-ctx Γ x ≡ Γ' ->
  --     (Γ' ⊢ e' ⇒)
  --   PreservationVarsSyn (SynConst consist) VSConst in-ctx refl = SynConst consist
  --   PreservationVarsSyn (SynHole consist) VSHole in-ctx refl = SynHole consist
  --   PreservationVarsSyn (SynFun consist syn) (VSFun {e-body' = e-body' ⇒ syn-body'} vars-syn) in-ctx refl = SynFun (preservation-lambda-lemma (vars-syn-beyond vars-syn) consist) (PreservationVarsSyn syn vars-syn (InCtxSkip in-ctx) refl)
  --   PreservationVarsSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} vars-syn-fun vars-syn-arg) in-ctx refl with ▸DTArrow-dec syn-fun' 
  --   ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (vars-syn-beyond vars-syn-fun) marrow marrow' 
  --   ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-consist-t t-out-beyond consist-syn) (beyond-consist-t t-in-beyond consist-ana) (beyond-consist-m m-beyond consist-mark) (PreservationVarsSyn syn vars-syn-fun in-ctx refl) (PreservationVarsAna ana vars-syn-arg in-ctx refl)
  --   PreservationVarsSyn {t = t} (SynVar in-ctx consist) VSVar in-ctx' refl with ∈NM-unicity in-ctx in-ctx' 
  --   ... | refl , refl = SynVar (oldify-access in-ctx) (▷DSome (MergeInfoOld refl))
  --   PreservationVarsSyn (SynVar in-ctx consist) (VSOtherVar neq) in-ctx' refl = SynVar (oldify-access-neq in-ctx neq) consist
  --   PreservationVarsSyn (SynAsc consist-syn consist-ana ana) (VSAsc vars-syn) in-ctx refl = SynAsc consist-syn consist-ana (PreservationVarsAna ana vars-syn in-ctx refl)
  
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
  PreservationStepAna ana step = {!   !}
  -- -- PreservationStepSyn (SynFun consist syn) (StepNewAnnFun {e-body' = e-body' ⇒ syn-body'} vars-syn) = SynFun (preservation-lambda-lemma-2 (vars-syn-beyond vars-syn)) (PreservationVarsSyn syn vars-syn InCtxFound refl)
  -- -- PreservationStepSyn (SynFun consist syn) (StepNewSynFun {t-asc = t-asc} {t-body} {n-asc}) = SynFun (direct-arrow-consist-lemma t-asc t-body n-asc Old) (oldify-syn syn)
  -- -- PreservationStepSyn (SynFun consist syn) (StepVoidSynFun {t-asc = t-asc} {t-body} {n-asc}) = SynFun (direct-arrow-consist-lemma t-asc t-body n-asc Old) (oldify-syn syn)

  -- well-typed-wrap : ∀ {Γ e syn} ->
  --   Γ ⊢ (e ⇒ syn) ⇒ ->
  --   Γ ⊢ ((e ⇒ syn) [ ✔ ]⇐ (□ , Old)) ⇐
  -- well-typed-wrap (SynConst x) = AnaSubsume SubsumableConst (~N-pair ~DVoidR) ▶Same (SynConst x)
  -- well-typed-wrap (SynHole x) = {!   !}
  -- well-typed-wrap (SynAp x x₁ x₂ x₃ syn x₄) = {!   !}
  -- well-typed-wrap (SynVar x x₁) = {!   !}
  -- well-typed-wrap (SynAsc x x₁ x₂) = {!   !}

  mutual 

    -- PreservationSynUnder : ∀ {Γ e e' syn syn'} ->
    --   Γ ⊢ (e ⇒ syn) [ ✔ ]⇐ (□ , Old) ⇐ ->
    --   ((e ⇒ syn) [ ✔ ]⇐ (□ , Old)) Low↦ ((e' ⇒ syn') [ ✔ ]⇐ (□ , Old)) ->
    --   Γ ⊢ (e' ⇒ syn') [ ✔ ]⇐ (□ , Old) ⇐
    -- PreservationSynUnder (AnaSubsume subsumable consist-t consist-m syn) (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)) = AnaSubsume {!   !} {!   !} {!   !} (PreservationSyn syn (StepUp fill1 step fill2))
    -- PreservationSynUnder (AnaSubsume subsumable consist-t consist-m syn) (StepLow x step x₂) = {!   !}
    -- PreservationSynUnder (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) step = {!   !}

    PreservationSyn :  
      ∀ {Γ e e'} ->
      (Γ ⊢ e ⇒) ->
      (e Up↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
    PreservationSyn (SynConst _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynHole _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    -- PreservationSyn (SynFun consist syn) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} FillU⊙)))) 
    --   = SynFun (preservation-lambda-lemma (beyond-U↦ step) consist) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))
    -- PreservationSyn (SynFun consist syn) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} (FillUEnvUpRec fill2))))) = SynFun consist (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙)))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-U↦ step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationSyn (SynVar _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec FillU⊙)))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))))
    PreservationSyn (SynConst _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynHole _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    -- PreservationSyn (SynFun {t-asc = t-asc , n-asc} consist syn) (StepLow {e-in' = (e' ⇒ syn') [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvFun FillL⊙)) step (FillLEnvUpRec (FillLEnvFun FillL⊙))) = SynFun {!   !} {!   !}
    -- PreservationSyn (SynFun {t-asc = t-asc , n-asc} consist syn) (StepLow (FillLEnvUpRec (FillLEnvFun FillL⊙)) (StepNewAnnFun {t-asc = t-asc'} vars-syn) (FillLEnvUpRec (FillLEnvFun FillL⊙))) rewrite new-max-r n-asc = SynFun {!  !} {!   !}
    -- PreservationSyn (SynFun consist syn) (StepLow (FillLEnvUpRec (FillLEnvFun FillL⊙)) StepNewSynFun (FillLEnvUpRec (FillLEnvFun FillL⊙))) = {!   !}
    -- PreservationSyn (SynFun consist syn) (StepLow (FillLEnvUpRec (FillLEnvFun FillL⊙)) StepVoidSynFun (FillLEnvUpRec (FillLEnvFun FillL⊙))) = {!   !}

    -- PreservationSyn (SynFun consist syn) (StepLow (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynFun consist (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = (e-fun' ⇒ syn-fun') [ ✔ ]⇐ (□ , Old)} (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp1 FillL⊙))) with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (beyond-L↦-inner step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (PreservationAna syn (StepLow FillL⊙ step FillL⊙)) ana 
    
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationAna syn (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2)))) ana 
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) = SynAp marrow consist-syn (beyond-▷-contra (beyond-L↦-env step FillL⊙ FillL⊙) consist-ana) consist-mark syn (PreservationAna ana (StepLow FillL⊙ step FillL⊙))  
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)))
    PreservationSyn (SynVar _ _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) = SynAsc consist-syn (beyond-▷■-contra (beyond-L↦-env step fill1 fill2) consist-ana) (PreservationAna ana (StepLow fill1 step fill2))
  

    -- tricky questions here. invariant or update need to be changed. 
    -- also, is there a better way to factor this? lemma about well typed lower when the upper inside takes a step, e.g.?
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
    PreservationAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepUp (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec fill1)))) step (FillUEnvLowRec (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} fill2))))) = AnaFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma (beyond-U↦-env step fill1 fill2) consist-syn) consist-all consist-m-all (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2))) 
    PreservationAna (AnaFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = (e' ⇒ syn') [ m' ]⇐ ana'} fill2)))) = AnaFun marrow consist (beyond-▷-contra (beyond-L↦-env step fill1 fill2) consist-ana) consist-asc consist-body ? consist-all consist-m-all (PreservationAna ana (StepLow fill1 step fill2))
  
    -- PreservationAna ana (StepLow FillL⊙ step FillL⊙) = PreservationStepAna ana step  
    -- PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepLow (FillLEnvLowRec (FillLEnvUpRec fill1)) step (FillLEnvLowRec (FillLEnvUpRec fill2))) = AnaSubsume (step-l-env-subsumable step fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2)))
    -- PreservationAna (AnaFun marrow ana consist consist-ana consist-asc consist-body edge) (StepLow (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun fill1))) step (FillLEnvLowRec (FillLEnvUpRec (FillLEnvFun {e' = e' [ m' ]⇐ ana'} fill2)))) = AnaFun marrow (PreservationAna ana (StepLow fill1 step fill2)) consist consist-ana consist-asc (beyond-consist-contra (beyond-L↦-env step fill1 fill2) consist-body) edge
    -- PreservationAna (AnaSubsume {ana-all = ana-all} subsumable consist-t consist-m syn) (StepUp {e-in' = e-all' ⇒ syn-all'} (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)) with ~D-dec syn-all' ana-all 
    -- ... | m' , consist-t' = AnaSubsume (step-subsumable step subsumable) consist-t' (beyond-consist-m (beyond-through-~D (beyond-U↦ step) consist-t consist-t') consist-m) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))
    -- PreservationAna (AnaSubsume subsumable consist-t consist-m syn) (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))) = AnaSubsume (step-u-env-subsumable step fill1 fill2 subsumable) consist-t consist-m (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    -- PreservationAna (AnaFun {t-in-ana = t-in-ana} marrow ana consist consist-ana consist-asc consist-body edge) (StepUp (FillUEnvLowRec FillU⊙) (StepNewAnnFun {t-asc = t-asc} vars-syn) (FillUEnvLowRec FillU⊙)) with ~NM-dec (t-asc , Old) t-in-ana
    -- ... | m-asc-ana' , consist' = AnaFun marrow (PreservationVarsAna ana vars-syn InCtxFound refl) consist' consist-ana (beyond-consist-m {!   !} consist-asc) consist-body {!   !}  
    -- PreservationAna (AnaFun marrow ana consist consist-ana consist-asc consist-body edge) (StepUp (FillUEnvLowRec FillU⊙) StepNewSynFun (FillUEnvLowRec FillU⊙)) = {!   !}    
    -- PreservationAna (AnaFun marrow ana consist consist-ana consist-asc consist-body edge) (StepUp (FillUEnvLowRec FillU⊙) StepVoidSynFun (FillUEnvLowRec FillU⊙)) = {!   !}                 
    -- PreservationAna (AnaFun marrow ana consist consist-ana consist-asc consist-body edge) (StepUp (FillUEnvLowRec (FillUEnvUpRec x₅)) step (FillUEnvLowRec (FillUEnvUpRec x₆))) = {!   !}    