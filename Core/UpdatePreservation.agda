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
open import Core.Merge
open import Core.Settled
-- open import Core.Lemmas-Context

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

  data =▷M : NewMark -> NewMark -> Set where 
    =▷MNew : ∀ {s m} -> 
      =▷M s (m , New)
    ▷MRefl : ∀ {s} -> 
      =▷M s s

  data =▷T : NewType -> NewType -> Set where 
    =▷TNew : ∀ {s t} -> 
      =▷T s (t , New)
    =▷TRefl : ∀ {s} -> 
      =▷T s s

  -- the "beyondness" relation - the latter is the unchanged or [New]
  data =▷D : TypeData -> TypeData -> Set where 
    =▷DNew : ∀ {s t} -> 
      =▷D s (■ (t , New))
    =▷DRefl : ∀ {s} -> 
      =▷D s s

  new-max-r : (n : Newness) -> n ⊓ New ≡ New 
  new-max-r Old = refl
  new-max-r New = refl
  
  ▷D-new : ∀ {t syn} -> ▷D (■ (t , New)) syn
  ▷D-new {syn = □} = ▷DVoidR
  ▷D-new {syn = ■ (t , n)} = ▷DSome MergeInfoNew

  new-through-▸DTArrowNM : ∀ {t t-in t-out m} ->
    ■ (t , New) ▸DTArrowNM t-in , t-out , m -> 
    ∃[ t-in' ] ∃[ t-out' ] ∃[ m' ] (t-in ≡ (t-in' , New) × t-out ≡ (t-out' , New) × m ≡ (m' , New))
  new-through-▸DTArrowNM (SynArrowSome (MNTArrowNew x)) = _ , _ , _ , refl , refl , refl

  new-through-~NM : ∀ {t1 t2 m} ->
    t1 ~NM (t2 , New) , m -> 
    ∃[ m' ] m ≡ (m' , New)
  new-through-~NM (NMConsist {n1 = n1} x) rewrite new-max-r n1 = _ , refl

  new-through-~D : ∀ {d t m} ->
    d ~D ■ (t , New) , m -> 
    ∃[ m' ] m ≡ (m' , New)
  new-through-~D ~DVoidL = ✔ , refl
  new-through-~D (~DSome (NMConsist {n1 = n1} x)) rewrite new-max-r n1 = _ , refl

  ▸TArrowM-dec : 
    (t : Type) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸TArrowM t-in , t-out , m
  ▸TArrowM-dec TBase = THole , THole , ✖ , MArrowBase
  ▸TArrowM-dec THole = THole , THole , ✔ , MArrowHole
  ▸TArrowM-dec (TArrow t1 t2) = t1 , t2 , ✔ , MArrowArrow

  ▸TArrowNM-dec : 
    (t : NewType) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸TArrowNM t-in , t-out , m
  ▸TArrowNM-dec (t , Old) with ▸TArrowM-dec t 
  ... | t-in , t-out , m , match = (t-in , Old) , (t-out , Old) , (m , Old) , MNTArrowOld match
  ▸TArrowNM-dec (t , New) with ▸TArrowM-dec t 
  ... | t-in , t-out , m , match = (t-in , New) , (t-out , New) , (m , New) , MNTArrowNew match

  ▸DTArrowNM-dec : 
    (syn : TypeData) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] syn ▸DTArrowNM t-in , t-out , m
  ▸DTArrowNM-dec □ = (THole , New) , (THole , New) , (✔ , New) , SynArrowNone
  ▸DTArrowNM-dec (■ t) with ▸TArrowNM-dec t 
  ... | t-in , t-out , m , match = t-in , t-out , m , SynArrowSome match


  ~M-dec : 
    (syn ana : Type) -> 
    ∃[ m ] syn ~M ana , m 
  ~M-dec TBase TBase = ✔ , ConsistBase
  ~M-dec TBase THole = ✔ , ConsistHoleR
  ~M-dec TBase (TArrow _ _) = ✖ , InconsistBaseArr
  ~M-dec THole TBase = ✔ , ConsistHoleL
  ~M-dec THole THole = ✔ , ConsistHoleR
  ~M-dec THole (TArrow _ _) = ✔ , ConsistHoleL
  ~M-dec (TArrow _ _) TBase = ✖ , InconsistArrBase
  ~M-dec (TArrow _ _) THole = ✔ , ConsistHoleR
  ~M-dec (TArrow syn1 syn2) (TArrow ana1 ana2) with ~M-dec syn1 ana1 | ~M-dec syn2 ana2 
  ... | m1 , consist1 | m2 , consist2 = (m1 ⊓M m2) , ConsistArr consist1 consist2

  ~NM-dec : 
    (syn ana : NewType) -> 
    ∃[ m ] syn ~NM ana , m 
  ~NM-dec (syn-t , syn-n) (ana-t , ana-n) with ~M-dec syn-t ana-t
  ... | m , consist = (m , (syn-n ⊓ ana-n)) , NMConsist consist

  ~D-dec : 
    (syn ana : TypeData) -> 
    ∃[ m ] syn ~D ana , m 
  ~D-dec □ _ = (✔ , New) , ~DVoidL
  ~D-dec (■ syn) □ = (✔ , New) , ~DVoidR
  ~D-dec (■ syn) (■ ana) with ~NM-dec syn ana 
  ... | m , consist = m , (~DSome consist)

  ▸TArrowM-unicity : ∀ {t t-in t-in' t-out t-out' m m'} ->
    t ▸TArrowM t-in , t-out , m -> 
    t ▸TArrowM t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸TArrowM-unicity MArrowBase MArrowBase = refl , refl , refl
  ▸TArrowM-unicity MArrowHole MArrowHole = refl , refl , refl
  ▸TArrowM-unicity MArrowArrow MArrowArrow = refl , refl , refl

  ▸TArrowNM-unicity : ∀ {t t-in t-in' t-out t-out' m m'} ->
    t ▸TArrowNM t-in , t-out , m -> 
    t ▸TArrowNM t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸TArrowNM-unicity (MNTArrowOld match1) (MNTArrowOld match2) with ▸TArrowM-unicity match1 match2
  ... | refl , refl , refl = refl , refl , refl
  ▸TArrowNM-unicity (MNTArrowNew match1) (MNTArrowNew match2) with ▸TArrowM-unicity match1 match2
  ... | refl , refl , refl = refl , refl , refl

  ▸DTArrowNM-unicity : ∀ {syn t-in t-in' t-out t-out' m m'} ->
    syn ▸DTArrowNM t-in , t-out , m -> 
    syn ▸DTArrowNM t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸DTArrowNM-unicity SynArrowNone SynArrowNone = refl , refl , refl
  ▸DTArrowNM-unicity (SynArrowSome match1) (SynArrowSome match2) = ▸TArrowNM-unicity match1 match2

  ∈NM-unicity : ∀ {x t t' Γ m m'} ->
    x , t ∈NM Γ , m ->
    x , t' ∈NM Γ , m' ->
    (t ≡ t' × m ≡ m')
  ∈NM-unicity InCtxEmpty InCtxEmpty = refl , refl
  ∈NM-unicity InCtxFound InCtxFound = refl , refl
  ∈NM-unicity (InCtxSkip in-ctx) (InCtxSkip in-ctx') = ∈NM-unicity in-ctx in-ctx'

  ▸DTArrowNM-=▷ : ∀ {syn syn' t-in t-in' t-out t-out' m m'} ->
    =▷D syn syn' ->
    syn ▸DTArrowNM t-in , t-out , m -> 
    syn' ▸DTArrowNM t-in' , t-out' , m' -> 
    (=▷T t-in t-in' × =▷T t-out t-out' × =▷M m m')
  ▸DTArrowNM-=▷ =▷DNew match1 (SynArrowSome (MNTArrowNew match2)) = =▷TNew , =▷TNew , =▷MNew
  ▸DTArrowNM-=▷ =▷DRefl match1 match2 with ▸DTArrowNM-unicity match1 match2 
  ... | refl , refl , refl = =▷TRefl , =▷TRefl , ▷MRefl

  beyond-consist-m : ∀ {m1 m1' m2} ->
    =▷M m1 m1' ->
    ▷NM m1 m2 ->
    ▷NM m1' m2 
  beyond-consist-m =▷MNew consist = ▷NMNew
  beyond-consist-m ▷MRefl consist = consist

  beyond-consist-t : ∀ {t t' syn} ->
    =▷T t t' ->
    ▷D (■ t) syn ->
    ▷D (■ t') syn
  beyond-consist-t =▷TNew consist = ▷D-new
  beyond-consist-t =▷TRefl consist = consist

  preservation-lambda-lemma : ∀ {t syn1 syn1' syn2} ->
    =▷D syn1 syn1' ->
    ▷D (SynArrow t syn1) syn2 ->
    ▷D (SynArrow t syn1') syn2
  preservation-lambda-lemma {t = t , n} =▷DNew match rewrite new-max-r n = ▷D-new
  preservation-lambda-lemma =▷DRefl match = match

  direct-arrow-consist-lemma : 
    (t1 t2 : Type) -> 
    (n1 n2 : Newness) ->
    ▷D (■ (NTArrow (t1 , n1) (t2 , n2))) (■ (TArrow t1 t2 , New))
  direct-arrow-consist-lemma t1 t2 Old Old = ▷DSome (MergeInfoOld refl)
  direct-arrow-consist-lemma t1 t2 Old New = ▷DSome MergeInfoNew
  direct-arrow-consist-lemma t1 t2 New Old = ▷DSome MergeInfoNew
  direct-arrow-consist-lemma t1 t2 New New = ▷DSome MergeInfoNew

  preservation-lambda-lemma-2 : ∀ {t1 t2 n syn} ->
    =▷D (■ (t2 , n)) syn -> 
    ▷D (SynArrow (t1 , Old) syn) (■ (TArrow t1 t2 , New))
  preservation-lambda-lemma-2 =▷DNew = ▷DSome MergeInfoNew
  preservation-lambda-lemma-2 {t1} {t2} {n} =▷DRefl = direct-arrow-consist-lemma t1 t2 Old n

  vars-syn-beyond : ∀ {x t e syn e' syn'} ->
    VarsSynthesize x t (e ⇒ syn) (e' ⇒ syn') -> 
    =▷D syn syn' 
  vars-syn-beyond VSConst = =▷DRefl
  vars-syn-beyond VSHole = =▷DRefl
  vars-syn-beyond (VSFun syn) = =▷DRefl
  vars-syn-beyond (VSAp syn syn₁) = =▷DRefl
  vars-syn-beyond VSVar = =▷DNew
  vars-syn-beyond (VSOtherVar x) = =▷DRefl
  vars-syn-beyond (VSAsc syn) = =▷DRefl

  -- this is imprecise : the =▷D relation is bigger than required. oh well. 
  step-syn-beyond : ∀ {e e' syn syn'} -> 
    (e ⇒ syn) U↦ (e' ⇒ syn') -> 
    =▷D syn syn' 
  step-syn-beyond (StepNewAnnFun _) = =▷DNew
  step-syn-beyond StepNewSynFun = =▷DNew
  step-syn-beyond StepVoidSynFun = =▷DNew
  step-syn-beyond (StepAp _) = =▷DNew
  step-syn-beyond StepAsc = =▷DNew


  -- stays the same, except possibly becomes old
  data ◁=D : TypeData -> TypeData -> Set where 
    ◁=DOld : ∀ {t n} -> 
      ◁=D (■ (t , n)) (■ (t , Old))
    ◁=DRefl : ∀ {t} -> ◁=D t t


  beyond-consist-contra : ∀ {t ana ana'} ->
    ◁=D ana ana' ->
    ▷D (■ t) ana ->
    ▷D (■ t) ana'
  beyond-consist-contra ◁=DOld (▷DSome MergeInfoNew) = ▷DSome MergeInfoNew
  beyond-consist-contra ◁=DOld (▷DSome (MergeInfoOld refl)) = ▷DSome (MergeInfoOld refl)
  beyond-consist-contra ◁=DRefl consist = consist

  step-ana-beyond : ∀ {e-in e-in' m m' ana ana'} -> 
    (e-in [ m ]⇐ ana) L↦ (e-in' [ m' ]⇐ ana') -> 
    ◁=D ana ana' 
  step-ana-beyond (StepNewSynConsist _) = ◁=DRefl
  step-ana-beyond (StepNewAnaConsist _ _) = ◁=DOld
  step-ana-beyond (StepAnaFun _ _) = ◁=DOld
  step-ana-beyond StepNoAnaFun = ◁=DRefl

  step-ana-env-beyond : ∀ {ε e e' e-in e-in' m m' ana ana'} -> 
    e L↦ e' -> 
    ε L⟦ e ⟧Low== (e-in [ m ]⇐ ana) ->
    ε L⟦ e' ⟧Low== (e-in' [ m' ]⇐ ana') ->
    ◁=D ana ana' 
  step-ana-env-beyond step FillL⊙ FillL⊙ = step-ana-beyond step
  step-ana-env-beyond step (FillLEnvLowRec x) (FillLEnvLowRec x₁) = ◁=DRefl

  oldify-▷D : ∀ {d t n} ->
    ▷D d (■ (t , n)) -> 
    ▷D d (■ (t , Old))
  oldify-▷D ▷DVoidL = ▷DVoidL
  oldify-▷D (▷DSome MergeInfoNew) = ▷DSome MergeInfoNew
  oldify-▷D (▷DSome (MergeInfoOld refl)) = ▷DSome (MergeInfoOld refl)

  oldify-syn : ∀ {Γ e t n} ->
    Γ ⊢ e ⇒ ■ (t , n) ⇒ ->
    Γ ⊢ e ⇒ ■ (t , Old) ⇒
  oldify-syn (SynConst consist) = SynConst (oldify-▷D consist)
  oldify-syn (SynHole consist) = SynHole (oldify-▷D consist)
  oldify-syn (SynFun consist syn) = SynFun (oldify-▷D consist) syn 
  oldify-syn (SynAp marrow consist-syn consist-ana consist-mark syn ana) = SynAp marrow (oldify-▷D consist-syn) consist-ana consist-mark syn ana
  oldify-syn (SynVar in-ctx consist consist-m) = SynVar in-ctx (oldify-▷D consist) consist-m
  oldify-syn (SynAsc consist-syn consist-ana ana) = SynAsc (oldify-▷D consist-syn) consist-ana ana

  newify-ana : ∀ {Γ e m ana t} ->
    Γ ⊢ e [ m ]⇐ ana ⇐ -> 
    Γ ⊢ e [ m ]⇐ ■ (t , New) ⇐
  newify-ana {t = t} (AnaSubsume {syn-all = syn-all} subsumable consist-t consist-m syn) with ~D-dec syn-all (■ (t , New)) 
  ... | _ , consist-m' with new-through-~D consist-m' 
  ... | _ , refl = AnaSubsume subsumable consist-m' ▷NMNew syn
  newify-ana {t = t-ana'} (AnaFun {t-asc = t-asc} marrow ana consist consist-ana consist-asc consist-body) with ▸DTArrowNM-dec (■ (t-ana' , New)) 
  ... | t-in-ana' , t-out-ana' , m-ana-ana' , marrow' with ~NM-dec t-asc t-in-ana' | new-through-▸DTArrowNM marrow' 
  ... | _ , consist' | a , b , c , refl , refl , refl with new-through-~NM consist'
  ... | _ , refl = AnaFun marrow' ana consist' ▷NMNew ▷NMNew ▷D-new

  oldify-ctx : Ctx -> ℕ -> Ctx 
  oldify-ctx ∅ x = ∅
  oldify-ctx ((t , n) ∷ Γ) zero = ((t , Old) ∷ Γ)
  oldify-ctx ((t , n) ∷ Γ) (suc x) = ((t , n) ∷ (oldify-ctx Γ x))

  oldify-access : ∀ {x t n Γ m} ->
    x , (t , n) ∈NM Γ , m ->
    x , (t , Old) ∈NM oldify-ctx Γ x , m
  oldify-access InCtxEmpty = InCtxEmpty
  oldify-access InCtxFound = InCtxFound
  oldify-access (InCtxSkip in-ctx) = InCtxSkip (oldify-access in-ctx)

  oldify-access-neq : ∀ {x y t Γ m} ->
    y , t ∈NM Γ , m ->
    ¬(y ≡ x) ->
    y , t ∈NM oldify-ctx Γ x , m
  oldify-access-neq InCtxEmpty neq = InCtxEmpty
  oldify-access-neq {x = zero} InCtxFound neq = ⊥-elim (neq refl)
  oldify-access-neq {x = suc x} InCtxFound neq = InCtxFound
  oldify-access-neq {x = zero} (InCtxSkip in-ctx) neq = InCtxSkip in-ctx
  oldify-access-neq {x = suc x} (InCtxSkip in-ctx) neq = InCtxSkip (oldify-access-neq in-ctx λ eq → neq (cong suc eq))
  
  PreservationVarsAna :
    ∀ {Γ Γ' x t e e' m ana} ->
    (Γ ⊢ (e [ m ]⇐ ana) ⇐) ->
    VarsSynthesize x t e e' ->
    x , (t , New) ∈NM Γ , (✔ , Old) ->
    oldify-ctx Γ x ≡ Γ' ->
    (Γ' ⊢ (e' [ m ]⇐ ana) ⇐)
  PreservationVarsAna = {!   !}

  PreservationVarsSyn :
    ∀ {Γ Γ' x t e e'} ->
    (Γ ⊢ e ⇒) ->
    VarsSynthesize x t e e' ->
    x , (t , New) ∈NM Γ , (✔ , Old) ->
    oldify-ctx Γ x ≡ Γ' ->
    (Γ' ⊢ e' ⇒)
  PreservationVarsSyn (SynConst consist) VSConst in-ctx refl = SynConst consist
  PreservationVarsSyn (SynHole consist) VSHole in-ctx refl = SynHole consist
  PreservationVarsSyn (SynFun consist syn) (VSFun {e-body' = e-body' ⇒ syn-body'} var-syn) in-ctx refl = SynFun (preservation-lambda-lemma (vars-syn-beyond var-syn) consist) (PreservationVarsSyn syn var-syn (InCtxSkip in-ctx) refl)
  PreservationVarsSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} var-syn-fun var-syn-arg) in-ctx refl with ▸DTArrowNM-dec syn-fun' 
  ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with ▸DTArrowNM-=▷ (vars-syn-beyond var-syn-fun) marrow marrow' 
  ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-consist-t t-out-beyond consist-syn) (beyond-consist-t t-in-beyond consist-ana) (beyond-consist-m m-beyond consist-mark) (PreservationVarsSyn syn var-syn-fun in-ctx refl) (PreservationVarsAna ana var-syn-arg in-ctx refl)
  PreservationVarsSyn {t = t} (SynVar in-ctx consist consist-m) VSVar in-ctx' refl with ∈NM-unicity in-ctx in-ctx' 
  ... | refl , refl = SynVar (oldify-access in-ctx) (▷DSome (MergeInfoOld refl)) consist-m
  PreservationVarsSyn (SynVar in-ctx consist consist-m) (VSOtherVar neq) in-ctx' refl = SynVar (oldify-access-neq in-ctx neq) consist consist-m
  PreservationVarsSyn (SynAsc consist-syn consist-ana ana) (VSAsc var-syn) in-ctx refl = SynAsc consist-syn consist-ana (PreservationVarsAna ana var-syn in-ctx refl)
  
  PreservationStepSyn :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇒) ->
    (e U↦ e') ->   
    (Γ ⊢ e' ⇒)
  PreservationStepSyn (SynConst _) ()
  PreservationStepSyn (SynHole _) ()
  PreservationStepSyn (SynFun consist syn) (StepNewAnnFun {e-body' = e-body' ⇒ syn-body'} vars-syn) = SynFun (preservation-lambda-lemma-2 (vars-syn-beyond vars-syn)) (PreservationVarsSyn syn vars-syn InCtxFound refl)
  PreservationStepSyn (SynFun consist syn) (StepNewSynFun {t-asc = t-asc} {t-body} {n-asc}) = SynFun (direct-arrow-consist-lemma t-asc t-body n-asc Old) (oldify-syn syn)
  PreservationStepSyn (SynFun consist syn) (StepVoidSynFun {t-asc = t-asc} {t-body} {n-asc}) = SynFun (direct-arrow-consist-lemma t-asc t-body n-asc Old) (oldify-syn syn)
  PreservationStepSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepAp marrow') = SynAp (SynArrowSome (MNTArrowOld marrow')) (▷DSome (MergeInfoOld refl)) (▷DSome (MergeInfoOld refl)) (▷NMOld refl) (oldify-syn syn) (newify-ana ana)
  PreservationStepSyn (SynVar _ _ _) ()
  PreservationStepSyn (SynAsc consist-syn consist-ana ana) StepAsc = SynAsc (▷DSome (MergeInfoOld refl)) (▷DSome (MergeInfoOld refl)) (newify-ana ana)
  
  PreservationStepAna :  
    ∀ {Γ e e'} ->
    (Γ ⊢ e ⇐) ->
    (e L↦ e') ->   
    (Γ ⊢ e' ⇐)
  PreservationStepAna ana step = {!   !}

  mutual 

    PreservationSyn :  
      ∀ {Γ e e'} ->
      (Γ ⊢ e ⇒) ->
      (e Up↦ e') ->   
      (Γ ⊢ e' ⇒)
    PreservationSyn syn (StepUp FillU⊙ step FillU⊙) = PreservationStepSyn syn step
    PreservationSyn (SynConst _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynHole _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynFun consist syn) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} FillU⊙)))) 
      = SynFun (preservation-lambda-lemma (step-syn-beyond step) consist) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙))
    PreservationSyn (SynFun consist syn) (StepUp (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvFun (FillUEnvLowRec {e' = e' ⇒ syn'} (FillUEnvUpRec fill2))))) = SynFun consist (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec FillU⊙)))) with ▸DTArrowNM-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with ▸DTArrowNM-=▷ (step-syn-beyond step) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = SynAp marrow' (beyond-consist-t t-out-beyond consist-syn) (beyond-consist-t t-in-beyond consist-ana) (beyond-consist-m m-beyond consist-mark) (PreservationSyn syn (StepUp FillU⊙ step FillU⊙)) ana
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp {e-in' = e-fun' ⇒ syn-fun'} (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAp1 (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationSyn syn (StepUp (FillUEnvUpRec fill1) step (FillUEnvUpRec fill2))) ana
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepUp (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill1))) step (FillUEnvUpRec (FillUEnvAp2 (FillUEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepUp (FillUEnvLowRec fill1) step (FillUEnvLowRec fill2)))
    PreservationSyn (SynVar _ _ _) (StepUp (FillUEnvUpRec ()) step (FillUEnvUpRec fill2))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec FillU⊙))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec FillU⊙)))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec FillU⊙) step (FillUEnvLowRec FillU⊙)))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepUp (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec (FillUEnvUpRec fill1)))) step (FillUEnvUpRec (FillUEnvAsc (FillUEnvLowRec (FillUEnvUpRec fill2))))) = SynAsc consist-syn consist-ana (PreservationAna ana (StepUp (FillUEnvLowRec (FillUEnvUpRec fill1)) step (FillUEnvLowRec (FillUEnvUpRec fill2))))
    PreservationSyn (SynConst _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynHole _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynFun consist ()) (StepLow (FillLEnvUpRec (FillLEnvFun FillL⊙)) StepNoAnaFun (FillLEnvUpRec (FillLEnvFun FillL⊙)))
    PreservationSyn (SynFun consist syn) (StepLow (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvFun (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynFun consist (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark () ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 FillL⊙)) StepNoAnaFun (FillLEnvUpRec (FillLEnvAp1 FillL⊙)))
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill1)))) step (FillLEnvUpRec (FillLEnvAp1 (FillLEnvLowRec (FillLEnvUpRec fill2))))) = SynAp marrow consist-syn consist-ana consist-mark (PreservationSyn syn (StepLow (FillLEnvUpRec fill1) step (FillLEnvUpRec fill2))) ana
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow {e-in' = e-in' [ m' ]⇐ ana'} (FillLEnvUpRec (FillLEnvAp2 FillL⊙)) step (FillLEnvUpRec (FillLEnvAp2 FillL⊙))) = SynAp marrow consist-syn (beyond-consist-contra (step-ana-env-beyond step FillL⊙ FillL⊙) consist-ana) consist-mark syn (PreservationAna ana (StepLow FillL⊙ step FillL⊙))  
    PreservationSyn (SynAp marrow consist-syn consist-ana consist-mark syn ana) (StepLow (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill1))) step (FillLEnvUpRec (FillLEnvAp2 (FillLEnvLowRec fill2)))) = SynAp marrow consist-syn consist-ana consist-mark syn (PreservationAna ana (StepLow (FillLEnvLowRec fill1) step (FillLEnvLowRec fill2)))
    PreservationSyn (SynVar _ _ _) (StepLow (FillLEnvUpRec ()) _ (FillLEnvUpRec _))
    PreservationSyn (SynAsc consist-syn consist-ana ana) (StepLow (FillLEnvUpRec (FillLEnvAsc fill1)) step (FillLEnvUpRec (FillLEnvAsc {e' = e-body' [ m-body' ]⇐ ana-body'} fill2))) = SynAsc consist-syn (beyond-consist-contra (step-ana-env-beyond step fill1 fill2) consist-ana) (PreservationAna ana (StepLow fill1 step fill2))

    PreservationAna :  
      ∀ {Γ e e'} ->
      (Γ ⊢ e ⇐) ->
      (e Low↦ e') ->   
      (Γ ⊢ e' ⇐)
    PreservationAna = {!   !}