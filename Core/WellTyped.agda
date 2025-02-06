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

data ▶ {A : Set} : NEW A -> A -> Set where 
  ▶New : ∀ {a a'} -> 
    ▶ (a , New) a' 
  ▶Old : ∀ {a} ->
    ▶ (a , Old) a

data ▷ {A : Set} : NEW A -> NEW A -> Set where 
  ▷Pair : ∀ {a a' n n'} -> 
    ▶ (a , n) a' ->
    ▷ (a , n) (a' , n')
    
data ▷■ {A : Set} : NEW A -> NEW (DATA A) -> Set where
  ▷■Pair : ∀ {a a' n n'} -> 
    ▷ (■ a , n) (a' , n') ->
    ▷■ (a , n) (a' , n')

-- -- Side conditions returning new marks. 

data _▸DTArrow_,_,_ : Data -> Data -> Data -> Mark -> Set where 
  DTArrowSome : ∀ {t t1 t2 m} ->
    t ▸TArrow t1 , t2 , m ->
    (■ t) ▸DTArrow (■ t1) , (■ t2) , (m)
  DTArrowNone : 
    □ ▸DTArrow □ , □ , ✔

data _▸NTArrow_,_,_ : NewData -> NewData -> NewData -> NewMark -> Set where 
  NTArrowC : ∀ {d n t1 t2 m} ->
    d ▸DTArrow t1 , t2 , m ->
    (d , n) ▸NTArrow (t1 , n) , (t2 , n) , (m , n)

  -- SynArrowNone : □ ▸DTArrowNM (THole , New) , (THole , New) , Any
  -- SynArrowSome : ∀ {t t1 t2 m} ->
  --   t ▸TArrowNM t1 , t2 , m -> 
  --   (■ t) ▸DTArrowNM t1 , t2 , m

data _,_∈N_,_ : ℕ -> NewType -> Ctx -> Mark -> Set where 
  InCtxEmpty : 
    0 , (THole , Old) ∈N ∅ , (✖)
  InCtxFound : ∀ {Γ t} -> 
    0 , t ∈N (t ∷ Γ) , (✔)
  InCtxSkip : ∀ {Γ t t' x m} -> 
    (x , t ∈N Γ , m) -> 
    (suc x , t ∈N (t' ∷ Γ) , m)

data _~D_,_ : Data -> Data -> Mark -> Set where 
  ~DVoidL : ∀ {d} ->
    □ ~D d , ✔
  ~DVoidR : ∀ {d} ->
    d ~D □ , ✔
  ~DSome : ∀ {d1 d2 m} ->
    d1 ~ d2 , m -> 
    (■ d1) ~D (■ d2) , m

data _■~D_,_ : Type -> Data -> Mark -> Set where 
  ■~D-pair : ∀ {t d m} ->
    (■ t) ~D d , m ->
    t ■~D d , m

data _~N_,_ : NewData -> NewData -> NewMark -> Set where 
  ~N-pair : ∀ {d1 d2 n1 n2 m} ->
    d1 ~D d2 , m -> 
    (d1 , n1) ~N (d2 , n2) , (m , n1 ⊓ n2)

data _■~N_,_ : NewType -> NewData -> NewMark -> Set where 
  ■~N-pair : ∀ {t n d m} ->
    (■ t , n) ~N d , m ->
    (t , n) ■~N d , m

DUnless : Data -> Data -> Data 
DUnless d □ = d
DUnless d (■ t) = □

NUnless : NewData -> NewData -> NewData 
NUnless (d1 , n1) (d2 , n2) = (DUnless d1 d2 , n1 ⊓ n2)

-- -- Legal arrangements of the synthesized, mark, and analyzed on a 
-- -- lambda in analytic position. Should be thought of as a predicate on 
-- -- syn and m as a function of ana. 
-- data AnaLamEdge : Data -> Mark -> Data -> Set where 
--   AnaLamVoid : ∀ {syn m n} ->
--     AnaLamEdge syn m (□ , n)
--   AnaLamNew : ∀ {syn m ana} ->
--     AnaLamEdge syn m (■ ana , New)
--   AnaLamOld : ∀ {ana} ->
--     AnaLamEdge □ ✔ (■ ana , Old)

DArrow : Type -> Data -> Data
DArrow t1 □ = □
DArrow t1 (■ t2) = ■ (TArrow t1 t2)

NArrow : NewType -> NewData -> NewData 
NArrow (t , n1) (d , n2) = (DArrow t d , n1 ⊓ n2)

-- -- Note: this version is not actually bidirectional. The two judgments are for
-- -- upper and lower expressions. The bidirectional invariant doesn't work; at a 
-- -- high level this is because mode is non-local, while the invariant must be 
-- -- local.

mutual 

  data _⊢_⇒ : (Γ : Ctx) (e : ExpUp) -> Set where 
    SynConst : ∀ {Γ syn-all} ->
      ▷ (■ TBase , Old) syn-all ->
      Γ ⊢ (EConst ⇒ syn-all) ⇒
    SynHole : ∀ {Γ syn-all} ->
      ▷ (■ THole , Old) syn-all ->
      Γ ⊢ (EHole ⇒ syn-all) ⇒
    -- SynFun : ∀ {Γ e-body syn-all syn-body ana-body t-asc m-ana m-asc m-body} ->
    --   ▷ (NArrow t-asc syn-body) syn-all ->
    --   (t-asc ∷ Γ) ⊢ ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body) ⇐ ->
    --   Γ ⊢ ((EFun t-asc m-ana m-asc ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body)) ⇒ syn-all) ⇒  
    SynAp : ∀ {Γ e-fun e-arg syn-all syn-fun ana-arg t-in-fun t-out-fun m-all m-fun m-arg} ->
      syn-fun ▸NTArrow t-in-fun , t-out-fun , m-fun -> 
      ▷ t-out-fun syn-all -> 
      ▷ t-in-fun ana-arg -> 
      ▶ m-fun m-all -> 
      Γ ⊢ ((e-fun ⇒ syn-fun) [ ✔ ]⇐ (□ , Old)) ⇐ ->
      -- Γ ⊢ (e-fun ⇒ syn-fun) ⇒ ->
      Γ ⊢ (e-arg [ m-arg ]⇐ ana-arg) ⇐ ->
      Γ ⊢ ((EAp ((e-fun ⇒ syn-fun) [ ✔ ]⇐ (□ , Old)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all) ⇒
    SynVar : ∀ {Γ x syn-all t-var m-var} ->
      x , t-var ∈N Γ , m-var ->
      ▷■ t-var syn-all ->
      Γ ⊢ ((EVar x m-var) ⇒ syn-all) ⇒
    SynAsc : ∀ {Γ e-body syn-all ana-body t-asc m-body} ->
      ▷■ (t-asc) syn-all -> 
      ▷■ (t-asc) ana-body -> 
      Γ ⊢ (e-body [ m-body ]⇐ ana-body) ⇐ ->
      Γ ⊢ ((EAsc t-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ⇒

  data _⊢_⇐ : (Γ : Ctx) (e : ExpLow) -> Set where 
    AnaSubsume : ∀ {Γ e-all syn-all ana-all m-all m-consist} ->
      SubsumableMid e-all ->
      syn-all ~N ana-all , m-consist ->
      ▶ m-consist m-all ->
      Γ ⊢ (e-all ⇒ syn-all) ⇒ -> 
      Γ ⊢ ((e-all ⇒ syn-all) [ m-all ]⇐ ana-all) ⇐ 
    AnaFun : ∀ {Γ e-body syn-all syn-body ana-all ana-body t-asc t-in-ana t-out-ana m-ana m-asc m-all m-body m-ana-ana m-asc-ana m-all-ana} ->
      -- analytic flow
      ana-all ▸NTArrow t-in-ana , t-out-ana , m-ana-ana -> 
      t-asc ■~N t-in-ana , m-asc-ana ->
      ▷ t-out-ana ana-body ->
      ▶ m-ana-ana m-ana -> 
      ▶ m-asc-ana m-asc -> 
      -- synthetic flow
      ▷ (NUnless (NArrow t-asc syn-body) ana-all) syn-all ->
      syn-all ~N ana-all , m-all-ana ->
      ▶ m-all-ana m-all -> 
      -- recursive call
      (t-asc ∷ Γ) ⊢ ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body) ⇐ ->
      Γ ⊢ (((EFun t-asc m-ana m-asc ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ ana-all) ⇐  
    
data _⇒ : Program -> Set where 
  SynProg : ∀ {e} ->
    ∅ ⊢ e ⇒ ->
    (Root e) ⇒