 
open import Data.Empty 
open import Data.Product
open import Relation.Binary.PropositionalEquality 

open import Prelude
open import Core.Core
open import Core.Marking

module Core.MarkingUnicity where

  ▸TArrow-unicity : ∀ {t t-in t-in' t-out t-out' m m'} ->
    t ▸TArrow t-in , t-out , m -> 
    t ▸TArrow t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸TArrow-unicity MArrowBase MArrowBase = refl , refl , refl
  ▸TArrow-unicity MArrowHole MArrowHole = refl , refl , refl
  ▸TArrow-unicity MArrowArrow MArrowArrow = refl , refl , refl

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

  ∈-unicity : ∀ {x t t' Γ m m'} ->
    x , t ∈ Γ , m ->
    x , t' ∈ Γ , m' ->
    (t ≡ t' × m ≡ m')
  ∈-unicity InCtxEmpty InCtxEmpty = refl , refl
  ∈-unicity InCtxFound InCtxFound = refl , refl
  ∈-unicity InCtxFound (InCtxSkip neq _) = ⊥-elim (neq refl)
  ∈-unicity (InCtxSkip neq _) InCtxFound = ⊥-elim (neq refl)
  ∈-unicity (InCtxSkip neq in-ctx) (InCtxSkip neq' in-ctx') = ∈-unicity in-ctx in-ctx'

  mutual 

    marking-unicity-syn : ∀{Γ b e e' t t'} ->
      Γ ⊢ b ~> e ⇒ t ->
      Γ ⊢ b ~> e' ⇒ t' ->
      e ≡ e' × t ≡ t'
    marking-unicity-syn MarkConst MarkConst = refl , refl
    marking-unicity-syn MarkHole MarkHole = refl , refl
    marking-unicity-syn (MarkVar in-ctx1) (MarkVar in-ctx2) 
      with ∈-unicity in-ctx1 in-ctx2 
    ... | refl , refl = refl , refl
    marking-unicity-syn (MarkAsc ana1) (MarkAsc ana2) 
      rewrite marking-unicity-ana ana1 ana2 = refl , refl
    marking-unicity-syn (MarkSynFun syn1) (MarkSynFun syn2) 
      with marking-unicity-syn syn1 syn2
    ... | refl , refl = refl , refl
    marking-unicity-syn (MarkAp syn1 marrow1 ana1) (MarkAp syn2 marrow2 ana2) 
      with marking-unicity-syn syn1 syn2
    ... | refl , refl with ▸TArrow-unicity marrow1 marrow2 
    ... | refl , refl , refl 
      rewrite marking-unicity-ana ana1 ana2 = refl , refl

    marking-unicity-ana : ∀{Γ b e e' t} ->
      Γ ⊢ b ~> e ⇐ t ->
      Γ ⊢ b ~> e' ⇐ t ->
      e ≡ e'
    marking-unicity-ana (MarkSubsume syn1 _ consist1) (MarkSubsume syn2 _ consist2) 
      with marking-unicity-syn syn1 syn2
    ... | refl , refl 
      rewrite ~-unicity consist1 consist2 = refl
    marking-unicity-ana (MarkAnaFun marrow1 ana1 consist1) (MarkAnaFun marrow2 ana2 consist2) 
      with ▸TArrow-unicity marrow1 marrow2 
    ... | refl , refl , refl 
      rewrite marking-unicity-ana ana1 ana2 
      rewrite ~-unicity consist1 consist2 = refl

  marking-unicity : ∀ {p p' p''} ->
    p ~> p' ->
    p ~> p'' ->
    p' ≡ p''
  marking-unicity (MarkProgram syn1) (MarkProgram syn2) with marking-unicity-syn syn1 syn2
  ... | refl , refl = refl