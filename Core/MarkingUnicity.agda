 
open import Data.Empty 
open import Data.Product
open import Relation.Binary.PropositionalEquality 

open import Prelude
open import Core.Core
open import Core.SideConditions
open import Core.Marking

module Core.MarkingUnicity where

  ∈-unicity : ∀ {A free x t t' m m'} -> {Γ : Context A free} ->
    x , t ∈ Γ , m ->
    x , t' ∈ Γ , m' ->
    (t ≡ t' × m ≡ m')
  ∈-unicity InCtxEmpty InCtxEmpty = refl , refl
  ∈-unicity InCtxFound InCtxFound = refl , refl
  ∈-unicity InCtxFound (InCtxSkip neq _) = ⊥-elim (neq refl)
  ∈-unicity (InCtxSkip neq _) InCtxFound = ⊥-elim (neq refl)
  ∈-unicity (InCtxSkip neq in-ctx) (InCtxSkip neq' in-ctx') = ∈-unicity in-ctx in-ctx'
  ∈-unicity (InCtxTSkip in-ctx) (InCtxTSkip in-ctx') = ∈-unicity in-ctx in-ctx'

  T∈-unicity : ∀ {A free x m m'} -> {Γ : Context A free} ->
    x T∈ Γ , m ->
    x T∈ Γ , m' ->
    m ≡ m'
  T∈-unicity InCtxEmpty InCtxEmpty = refl
  T∈-unicity InCtxFound InCtxFound = refl
  T∈-unicity InCtxFound (InCtxTSkip neq in-ctx2) = ⊥-elim (neq refl)
  T∈-unicity (InCtxSkip in-ctx1) (InCtxSkip in-ctx2) = T∈-unicity in-ctx1 in-ctx2
  T∈-unicity (InCtxTSkip neq in-ctx1) InCtxFound = ⊥-elim (neq refl)
  T∈-unicity (InCtxTSkip neq1 in-ctx1) (InCtxTSkip neq2 in-ctx2) = T∈-unicity in-ctx1 in-ctx2

  marking-unicity-typ : ∀{Γ b t t'} ->
      Γ ⊢ b T~> t ->
      Γ ⊢ b T~> t' ->
      t ≡ t'
  marking-unicity-typ MarkBase MarkBase = refl
  marking-unicity-typ MarkHole MarkHole = refl
  marking-unicity-typ (MarkArrow typ1 typ2) (MarkArrow typ3 typ4) 
    rewrite marking-unicity-typ typ1 typ3
    rewrite marking-unicity-typ typ2 typ4 = refl
  marking-unicity-typ (MarkProd typ1 typ2) (MarkProd typ3 typ4)
    rewrite marking-unicity-typ typ1 typ3
    rewrite marking-unicity-typ typ2 typ4 = refl
  marking-unicity-typ (MarkTVar in-ctx1) (MarkTVar in-ctx2) 
    rewrite T∈-unicity in-ctx1 in-ctx2 = refl
  marking-unicity-typ (MarkForall typ1) (MarkForall typ2)
    rewrite marking-unicity-typ typ1 typ2 = refl

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
    marking-unicity-syn (MarkAsc typ1 ana1) (MarkAsc typ2 ana2) 
      rewrite marking-unicity-typ typ1 typ2
      rewrite marking-unicity-ana ana1 ana2 = refl , refl
    marking-unicity-syn (MarkSynFun typ1 syn1) (MarkSynFun typ2 syn2)
      rewrite marking-unicity-typ typ1 typ2
      with marking-unicity-syn syn1 syn2
    ... | refl , refl = refl , refl
    marking-unicity-syn (MarkAp syn1 marrow1 ana1) (MarkAp syn2 marrow2 ana2) 
      with marking-unicity-syn syn1 syn2
    ... | refl , refl with ▸TArrow-unicity marrow1 marrow2 
    ... | refl , refl , refl 
      rewrite marking-unicity-ana ana1 ana2 = refl , refl
    marking-unicity-syn (MarkSynPair syn1 syn2) (MarkSynPair syn3 syn4)
      with marking-unicity-syn syn1 syn3 | marking-unicity-syn syn2 syn4
    ... | refl , refl | refl , refl = refl , refl
    marking-unicity-syn (MarkProj syn1 marrow1) (MarkProj syn2 marrow2)
      with marking-unicity-syn syn1 syn2
    ... | refl , refl with ▸TProj-unicity marrow1 marrow2
    ... | refl , refl = refl , refl
    marking-unicity-syn (MarkSynTypFun syn1) (MarkSynTypFun syn2) 
      with marking-unicity-syn syn1 syn2
    ... | refl , refl = refl , refl
    marking-unicity-syn (MarkTypAp syn1 mforall1 typ1 sub1) (MarkTypAp syn2 mforall2 typ2 sub2) 
      with marking-unicity-syn syn1 syn2
    ... | refl , refl with ▸TForall-unicity mforall1 mforall2 
    ... | refl , refl , refl 
      rewrite marking-unicity-typ typ1 typ2
      rewrite sub-unicity sub1 sub2 = refl , refl

    marking-unicity-ana : ∀{Γ b e e' t} ->
      Γ ⊢ b ~> e ⇐ t ->
      Γ ⊢ b ~> e' ⇐ t ->
      e ≡ e'
    marking-unicity-ana (MarkSubsume syn1 _ consist1) (MarkSubsume syn2 _ consist2) 
      with marking-unicity-syn syn1 syn2
    ... | refl , refl 
      rewrite ~-unicity consist1 consist2 = refl
    marking-unicity-ana (MarkAnaFun typ1 marrow1 ana1 consist1) (MarkAnaFun typ2 marrow2 ana2 consist2) 
      with ▸TArrow-unicity marrow1 marrow2 
    ... | refl , refl , refl 
      rewrite marking-unicity-typ typ1 typ2
      rewrite marking-unicity-ana ana1 ana2 
      rewrite ~-unicity consist1 consist2 = refl
    marking-unicity-ana (MarkAnaPair mprod1 ana1 ana2) (MarkAnaPair mprod2 ana3 ana4)
      with ▸TProd-unicity mprod1 mprod2 
    ... | refl , refl , refl 
      rewrite marking-unicity-ana ana1 ana3 
      rewrite marking-unicity-ana ana2 ana4 = refl 
    marking-unicity-ana (MarkAnaTypFun mforall1 ana1) (MarkAnaTypFun mforall2 ana2) 
      with ▸TForallBind-unicity mforall1 mforall2 
    ... | refl , refl 
      rewrite marking-unicity-ana ana1 ana2 = refl

  marking-unicity : ∀ {p p' p''} ->
    p ~> p' ->
    p ~> p'' ->
    p' ≡ p''
  marking-unicity (MarkProgram syn1) (MarkProgram syn2) with marking-unicity-syn syn1 syn2
  ... | refl , refl = refl