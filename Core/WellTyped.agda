open import Data.Nat hiding (_+_; _⊓_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.WellTyped where

-- Directed Newness Consistency Judgments:
-- Tests whether the first piece of data (which has been calculated 
-- from slightly upstream in the information flow) is consistent with the 
-- second (which is found as an annotation slghtly downstream). 

data _▷NT_ : NewType -> NewType -> Set where 
  MergeInfoNew : ∀ {t1 t2 n2} -> 
    (t1 , New) ▷NT (t2 , n2)
  MergeInfoOld : ∀ {t1 t2 n2} -> 
    (t1 ≡ t2) -> (t1 , Old) ▷NT (t2 , n2)

data ▷D : TypeData -> TypeData -> Set where 
  ▷DVoidL : ∀ {s} -> 
    ▷D □ s
  ▷DVoidR : ∀ {s} -> 
    ▷D s □
  ▷DSome : ∀ {syn1 syn2} -> 
    syn1 ▷NT syn2 ->
    ▷D (■ syn1) (■ syn2)

data ▷NM : (m1 : NewMark) (m2 : MarkData) -> Set where 
  ▷NMNew : ∀ {m1 m2} ->
    ▷NM (m1 , New) m2
  ▷NMOld : ∀ {m1 m2} ->
    (m1 ≡ m2) -> ▷NM (m1 , Old) m2

-- Side conditions returning new marks. 

data _▸TArrowNM_,_,_ : NewType -> NewType -> NewType -> NewMark -> Set where 
  MNTArrowOld : ∀ {t t1 t2 m} ->
    t ▸TArrowM t1 , t2 , m ->
    (t , Old) ▸TArrowNM (t1 , Old) , (t2 , Old) , (m , Old)
  MNTArrowNew : ∀ {t t1 t2 m} ->
    t ▸TArrowM t1 , t2 , m ->
    (t , New) ▸TArrowNM (t1 , New) , (t2 , New) , (m , New)

data _▸DTArrowNM_,_,_ : TypeData -> NewType -> NewType -> NewMark -> Set where 
  SynArrowNone : □ ▸DTArrowNM (THole , New) , (THole , New) , (✔ , New)
  SynArrowSome : ∀ {t t1 t2 m} ->
    t ▸TArrowNM t1 , t2 , m -> 
    (■ t) ▸DTArrowNM t1 , t2 , m

data _,_∈NM_,_ : ℕ -> NewType -> Ctx -> MarkData -> Set where 
  InCtxEmpty : 
    0 , (THole , Old) ∈NM ∅ , ✖ 
  InCtxFound : ∀ {Γ t} -> 
    0 , t ∈NM (t ∷ Γ) , ✔
  InCtxSkip : ∀ {Γ t t' x m} -> 
    (x , t ∈NM Γ , m) -> 
    (suc x , t ∈NM (t' ∷ Γ) , m)

data _~NM_,_ : NewType -> NewType -> NewMark -> Set where 
  NMConsist : ∀ {t1 t2 n1 n2 m} ->
    t1 ~M t2 , m -> 
    (t1 , n1) ~NM (t2 , n2) , (m , n1 ⊓ n2) 

data _~D_,_ : TypeData -> TypeData -> NewMark -> Set where 
  ~DVoidL : ∀ {d} ->
     □ ~D d , (✔ , New)
  ~DVoidR : ∀ {d} ->
    d ~D □ , (✔ , New)
  ~DSome : ∀ {d1 d2 m} ->
    d1 ~NM d2 , m -> 
    (■ d1) ~D (■ d2) , m

-- Legal arrangements of the synthesized, mark, and analyzed on a 
-- lambda in analytic position. Should be thought of as a predicate on 
-- syn and m as a function of ana. 
data AnaLamEdge : TypeData -> MarkData -> TypeData -> Set where 
  AnaLamVoid : ∀ {syn m} ->
    AnaLamEdge syn m □
  AnaLamNew : ∀ {syn m ana} ->
    AnaLamEdge syn m (■ (ana , New))
  AnaLamOld : ∀ {ana} ->
    AnaLamEdge □ ✔ (■ (ana , Old))

NTArrow : NewType -> NewType -> NewType
NTArrow (t1 , n1) (t2 , n2) = ( TArrow t1 t2 , n1 ⊓ n2 )

SynArrow : NewType -> TypeData -> TypeData 
SynArrow t □ = □
SynArrow t1 (■ t2) = ■ (NTArrow t1 t2)

mutual 

  data _⊢_⇒ : (Γ : Ctx) (e : ExpUp) -> Set where 
    SynConst : ∀ {Γ syn-all} ->
      ▷D (■ (TBase , Old)) syn-all ->
      Γ ⊢ (EConst ⇒ syn-all) ⇒
    SynHole : ∀ {Γ syn-all} ->
      ▷D (■ (THole , Old)) syn-all ->
      Γ ⊢ (EHole ⇒ syn-all) ⇒
    SynFun : ∀ {Γ e-body syn-all syn-body ana-body t-asc m-ana m-asc m-body} ->
      ▷D (SynArrow t-asc syn-body) syn-all ->
      (t-asc ∷ Γ) ⊢ (e-body ⇒ syn-body) ⇒ ->
      Γ ⊢ ((EFun t-asc m-ana m-asc ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body)) ⇒ syn-all) ⇒
    SynAp : ∀ {Γ e-fun e-arg syn-all syn-fun ana-arg t-in-fun t-out-fun m-all m-fun m-arg} ->
      syn-fun ▸DTArrowNM t-in-fun , t-out-fun , m-fun -> 
      ▷D (■ t-out-fun) syn-all -> 
      ▷D (■ t-in-fun) ana-arg -> 
      ▷NM m-fun m-all -> 
      Γ ⊢ (e-fun ⇒ syn-fun) ⇒ ->
      Γ ⊢ (e-arg [ m-arg ]⇐ ana-arg) ⇐ ->
      Γ ⊢ ((EAp ((e-fun ⇒ syn-fun) [ ✔ ]⇐ □) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all) ⇒
    SynVar : ∀ {Γ x syn-all t-var m-var} ->
      x , t-var ∈NM Γ , m-var ->
      ▷D (■ t-var) syn-all ->
      Γ ⊢ ((EVar x m-var) ⇒ syn-all) ⇒
    SynAsc : ∀ {Γ e-body syn-all ana-body t-asc m-body} ->
      ▷D (■ t-asc) syn-all -> 
      ▷D (■ t-asc) ana-body -> 
      Γ ⊢ (e-body [ m-body ]⇐ ana-body) ⇐ ->
      Γ ⊢ ((EAsc t-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ⇒

  data _⊢_⇐ : (Γ : Ctx) (e : ExpLow) -> Set where 
    AnaSubsume : ∀ {Γ e-all syn-all ana-all m-all m-consist} ->
      SubsumableMid e-all ->
      syn-all ~D ana-all , m-consist ->
      ▷NM m-consist m-all ->
      Γ ⊢ (e-all ⇒ syn-all) ⇒ -> 
      Γ ⊢ ((e-all ⇒ syn-all) [ m-all ]⇐ ana-all) ⇐ 
    AnaFun : ∀ {Γ e-body syn-all ana-all ana-body t-asc t-in-ana t-out-ana m-ana m-asc m-all m-body m-ana-ana m-asc-ana} ->
      ana-all ▸DTArrowNM t-in-ana , t-out-ana , m-ana-ana -> 
      (t-asc ∷ Γ) ⊢ (e-body [ m-body ]⇐ ana-body) ⇐ ->
      t-asc ~NM t-in-ana , m-asc-ana ->
      ▷NM m-ana-ana m-ana -> 
      ▷NM m-asc-ana m-asc -> 
      ▷D (■ t-out-ana) ana-body ->
      AnaLamEdge syn-all m-all ana-all ->
      Γ ⊢ (((EFun t-asc m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ ana-all) ⇐  
    
data _⇒ : Program -> Set where 
  SynProg : ∀ {e} ->
    ∅ ⊢ e ⇒ ->
    (Root e) ⇒