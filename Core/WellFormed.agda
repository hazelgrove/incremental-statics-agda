
open import Data.Unit 
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.SideConditions

module Core.WellFormed where

  data ▶ {A : Set} : ○ A -> A -> Set where 
    ▶★ : ∀ {a a'} -> 
      ▶ (a , ★) a' 
    ▶• : ∀ {a} ->
      ▶ (a , •) a

  data ▷ {A : Set} : ○ A -> ○ A -> Set where 
    ▷Pair : ∀ {a a' n n'} -> 
      ▶ (a , n) a' ->
      ▷ (a , n) (a' , n')
      
  data ▷■ : ○Type -> ○Data -> Set where
    ▷■Pair : ∀ {a a' n n'} -> 
      ▷ (■ a , n) (a' , n') ->
      ▷■ (a , n) (a' , n')

  data _▸DTArrow_,_,_ : Data -> Data -> Data -> Mark -> Set where 
    DTArrowSome : ∀ {t t1 t2 m} ->
      t ▸TArrow t1 , t2 , m ->
      (■ t) ▸DTArrow (■ t1) , (■ t2) , (m)
    DTArrowNone : 
      □ ▸DTArrow □ , □ , ✔

  data _▸NTArrow_,_,_ : ○Data -> ○Data -> ○Data -> ○Mark -> Set where 
    NTArrowC : ∀ {d n t1 t2 m} ->
      d ▸DTArrow t1 , t2 , m ->
      (d , n) ▸NTArrow (t1 , n) , (t2 , n) , (m , n)

  data _▸DTProd_,_,_ : Data -> Data -> Data -> Mark -> Set where 
    DTProdSome : ∀ {t t1 t2 m} ->
      t ▸TProd t1 , t2 , m ->
      (■ t) ▸DTProd (■ t1) , (■ t2) , (m)
    DTProdNone : 
      □ ▸DTProd □ , □ , ✔

  data _▸NTProd_,_,_ : ○Data -> ○Data -> ○Data -> ○Mark -> Set where 
    NTProdC : ∀ {d n t1 t2 m} ->
      d ▸DTProd t1 , t2 , m ->
      (d , n) ▸NTProd (t1 , n) , (t2 , n) , (m , n) 

  data _,_▸DTProj_,_ : Data -> ProdSide -> Data -> Mark -> Set where
    DTProjSome : ∀ {t s t' m} -> 
      t , s ▸TProj t' , m ->
      (■ t) , s ▸DTProj (■ t') , m
    DTProjNone : ∀ {s} -> 
      □ , s ▸DTProj □ , ✔
  
  data _,_▸NTProj_,_ : ○Data -> ProdSide -> ○Data -> ○Mark -> Set where
    NTProjC : ∀ {d s n t m} ->
      d , s ▸DTProj t , m ->
      (d , n) , s ▸NTProj (t , n) , (m , n)

  -- data _,_∈N_,_ : Var -> ○Type -> Ctx -> Mark -> Set where 
  --   InCtxEmpty : ∀ {x} ->
  --     x ,  (THole , •) ∈N ∅ , ✖ 
  --   InCtxFound : ∀ {Γ x t} ->
  --     x , t ∈N (x ∶ t ∷ Γ) , ✔
  --   InCtxSkip : ∀ {Γ t t' x x' m} -> 
  --     ¬(x ≡ x') ->
  --     (x , t ∈N Γ , m) -> 
  --     (x , t ∈N (x' ∶ t' ∷ Γ) , m)

  -- _,_∈N?_,_ : Binding -> ○Type -> Ctx -> Mark -> Set
  -- BHole , t ∈N? Γ , m = ⊤
  -- BVar x , t ∈N? Γ , m = x , t ∈N Γ , m

  -- InCtxSkip? : ∀ {x' x  Γ t t' m} -> 
  --   ¬((BVar x) ≡ x') ->
  --   (x , t ∈N Γ , m) -> 
  --   (x , t ∈N (x' ∶ t' ∷? Γ) , m)
  -- InCtxSkip? {BHole} neq in-ctx = in-ctx
  -- InCtxSkip? {BVar x} neq in-ctx = InCtxSkip (λ eq → neq (cong BVar eq)) in-ctx

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

  data _~N_,_ : ○Data -> ○Data -> ○Mark -> Set where 
    ~N-pair : ∀ {d1 d2 n1 n2 m} ->
      d1 ~D d2 , m -> 
      (d1 , n1) ~N (d2 , n2) , (m , n1 ⊓ n2)

  data _■~N_,_ : ○Type -> ○Data -> ○Mark -> Set where 
    ■~N-pair : ∀ {t n d m} ->
      (■ t , n) ~N d , m ->
      (t , n) ■~N d , m

  DUnless : Data -> Data -> Data 
  DUnless d □ = d
  DUnless d (■ t) = □

  NUnless : ○Data -> ○Data -> ○Data 
  NUnless (d , n1) (■ t , n2) = (□ , n2)
  NUnless (d , n1) (□ , n2) = (d , n1 ⊓ n2)

  DArrow : Type -> Data -> Data
  DArrow t1 □ = □
  DArrow t1 (■ t2) = ■ (TArrow t1 t2)

  NArrow : ○Type -> ○Data -> ○Data 
  NArrow (t , n1) (d , n2) = (DArrow t d , n1 ⊓ n2)

  DProd : Data -> Data -> Data
  DProd t1 □ = □
  DProd □ t2 = □
  DProd (■ t1) (■ t2) = ■ (TProd t1 t2)

  NProd : ○Data -> ○Data -> ○Data 
  NProd (d1 , n1) (d2 , n2) = (DProd d1 d2 , n1 ⊓ n2)

  mutual 

    data _S⊢_ : (Γ : Ctx) (e : SynExp) -> Set where 
      WFConst : ∀ {Γ syn-all} ->
        ▷ (■ TBase , •) syn-all ->
        Γ S⊢ (EConst ⇒ syn-all)
      WFHole : ∀ {Γ syn-all} ->
        ▷ (■ THole , •) syn-all ->
        Γ S⊢ (EHole ⇒ syn-all)
      WFAp : ∀ {Γ e-fun e-arg syn-all syn-fun ana-arg t-in-fun t-out-fun m-all m-fun m-arg n} ->
        syn-fun ▸NTArrow t-in-fun , t-out-fun , m-fun -> 
        ▷ t-out-fun syn-all -> 
        ▷ t-in-fun ana-arg -> 
        ▶ m-fun m-all -> 
        Γ L⊢ ((e-fun ⇒ syn-fun) [ ✔ ]⇐ (□ , n)) ->
        Γ L⊢ (e-arg [ m-arg ]⇐ ana-arg) ->
        Γ S⊢ ((EAp ((e-fun ⇒ syn-fun) [ ✔ ]⇐ (□ , n)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all)
      WFVar : ∀ {Γ x syn-all t-var m-var n-syn} ->
        x , t-var ∈ Γ , m-var ->
        ▷ t-var (syn-all , n-syn) ->
        Γ S⊢ ((EVar x m-var) ⇒ (■ syn-all , n-syn))
      WFAsc : ∀ {Γ e-body syn-all ana-body t-asc m-body n-syn n-ana} ->
        ▷ t-asc (syn-all , n-syn) -> 
        ▷ t-asc (ana-body , n-ana) -> 
        Γ L⊢ (e-body [ m-body ]⇐ (■ ana-body , n-ana)) ->
        Γ S⊢ ((EAsc t-asc (e-body [ m-body ]⇐ (■ ana-body , n-ana))) ⇒ (■ syn-all , n-syn))
      WFProj : ∀ {Γ s e-body syn-body syn-all t-side-body m-body m-all n} ->
        syn-body , s ▸NTProj t-side-body , m-body -> 
        ▷ t-side-body syn-all -> 
        ▶ m-body m-all -> 
        Γ L⊢ ((e-body ⇒ syn-body) [ ✔ ]⇐ (□ , n)) ->
        Γ S⊢ ((EProj s ((e-body ⇒ syn-body) [ ✔ ]⇐ (□ , n)) m-all) ⇒ syn-all)

    data _L⊢_ : (Γ : Ctx) (e : AnaExp) -> Set where 
      WFSubsume : ∀ {Γ e-all syn-all ana-all m-all m-consist} ->
        SubsumableMid e-all ->
        syn-all ~N ana-all , m-consist ->
        ▶ m-consist m-all ->
        Γ S⊢ (e-all ⇒ syn-all) -> 
        Γ L⊢ ((e-all ⇒ syn-all) [ m-all ]⇐ ana-all)
      WFFun : ∀ {Γ x e-body syn-all syn-body ana-all ana-body t-asc t-in-ana t-out-ana m-ana m-asc m-all m-body m-ana-ana m-asc-ana m-all-ana} ->
        ana-all ▸NTArrow t-in-ana , t-out-ana , m-ana-ana -> 
        t-asc ■~N t-in-ana , m-asc-ana ->
        ▷ t-out-ana ana-body ->
        ▶ m-ana-ana m-ana -> 
        ▶ m-asc-ana m-asc -> 
        ▷ (NUnless (NArrow t-asc syn-body) ana-all) syn-all -> -- <-- this step also flows from ana
        syn-all ~N ana-all , m-all-ana ->
        ▶ m-all-ana m-all -> 
        (x ∶ t-asc ∷? Γ) L⊢ ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body) ->
        Γ L⊢ (((EFun x t-asc m-ana m-asc ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ ana-all)  
      WFPair : ∀ {Γ e-fst e-snd syn-all syn-fst syn-snd ana-all ana-fst ana-snd t-fst-ana t-snd-ana m-ana m-fst m-snd m-all m-ana-ana m-all-ana} ->
        ana-all ▸NTProd t-fst-ana , t-snd-ana , m-ana-ana -> 
        ▷ t-fst-ana ana-fst -> 
        ▷ t-snd-ana ana-snd -> 
        ▶ m-ana-ana m-ana -> 
        ▷ (NUnless (NProd syn-fst syn-snd) ana-all) syn-all -> 
        syn-all ~N ana-all , m-all-ana ->
        ▶ m-all-ana m-all -> 
        Γ L⊢ ((e-fst ⇒ syn-fst) [ m-fst ]⇐ ana-fst) ->
        Γ L⊢ ((e-snd ⇒ syn-snd) [ m-snd ]⇐ ana-snd) ->
        Γ L⊢ (((EPair ((e-fst ⇒ syn-fst) [ m-fst ]⇐ ana-fst) ((e-snd ⇒ syn-snd) [ m-snd ]⇐ ana-snd) m-ana) ⇒ syn-all) [ m-all ]⇐ ana-all)  
      
  data P⊢ : Program -> Set where 
    WFProgram : ∀ {p} ->
      (∅ (THole , •)) L⊢ (AnaExpOfProgram p) ->
      P⊢ p