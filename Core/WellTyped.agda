
open import Data.Unit 
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core

module Core.WellTyped where

  data ▶ {A : Set} : NEW A -> A -> Set where 
    ▶New : ∀ {a a'} -> 
      ▶ (a , New) a' 
    ▶Old : ∀ {a} ->
      ▶ (a , Old) a

  ▷ : {A : Set} -> NEW A -> NEW A -> Set 
  ▷ (a , n) (a' , n') =  ▶ (a , n) a'
      
  ▷■ : NewType -> NewData -> Set
  ▷■ (a , n) (a' , n') = ▷ (■ a , n) (a' , n')

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

  data _,_∈N_,_ : Var -> NewType -> Ctx -> Mark -> Set where 
    InCtxEmpty : ∀ {x} ->
      x ,  (THole , Old) ∈N ∅ , ✖ 
    InCtxFound : ∀ {Γ x t} ->
      x , t ∈N (x ∶ t ∷ Γ) , ✔
    InCtxSkip : ∀ {Γ t t' x x' m} -> 
      ¬(x ≡ x') ->
      (x , t ∈N Γ , m) -> 
      (x , t ∈N (x' ∶ t' ∷ Γ) , m)

  _,_∈N?_,_ : Binding -> NewType -> Ctx -> Mark -> Set
  BHole , t ∈N? Γ , m = ⊤
  BVar x , t ∈N? Γ , m = x , t ∈N Γ , m

  InCtxSkip? : ∀ {x' x  Γ t t' m} -> 
    ¬((BVar x) ≡ x') ->
    (x , t ∈N Γ , m) -> 
    (x , t ∈N (x' ∶ t' ∷? Γ) , m)
  InCtxSkip? {BHole} neq in-ctx = in-ctx
  InCtxSkip? {BVar x} neq in-ctx = InCtxSkip (λ eq → neq (cong BVar eq)) in-ctx

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
  NUnless (d , n1) (■ t , n2) = (□ , n2)
  NUnless (d , n1) (□ , n2) = (d , n1 ⊓ n2)

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
      SynAp : ∀ {Γ e-fun e-arg syn-all syn-fun ana-arg t-in-fun t-out-fun m-all m-fun m-arg n} ->
        syn-fun ▸NTArrow t-in-fun , t-out-fun , m-fun -> 
        ▷ t-out-fun syn-all -> 
        ▷ t-in-fun ana-arg -> 
        ▶ m-fun m-all -> 
        Γ ⊢ ((e-fun ⇒ syn-fun) [ ✔ ]⇐ (□ , n)) ⇐ ->
        Γ ⊢ (e-arg [ m-arg ]⇐ ana-arg) ⇐ ->
        Γ ⊢ ((EAp ((e-fun ⇒ syn-fun) [ ✔ ]⇐ (□ , n)) m-all (e-arg [ m-arg ]⇐ ana-arg)) ⇒ syn-all) ⇒
      SynVar : ∀ {Γ x syn-all t-var m-var n-syn} ->
        x , t-var ∈N Γ , m-var ->
        ▷ t-var (syn-all , n-syn) ->
        Γ ⊢ ((EVar x m-var) ⇒ (■ syn-all , n-syn)) ⇒
      SynAsc : ∀ {Γ e-body syn-all ana-body t-asc m-body n-syn n-ana} ->
        ▷ t-asc (syn-all , n-syn) -> 
        ▷ t-asc (ana-body , n-ana) -> 
        Γ ⊢ (e-body [ m-body ]⇐ (■ ana-body , n-ana)) ⇐ ->
        Γ ⊢ ((EAsc t-asc (e-body [ m-body ]⇐ (■ ana-body , n-ana))) ⇒ (■ syn-all , n-syn)) ⇒

    data _⊢_⇐ : (Γ : Ctx) (e : ExpLow) -> Set where 
      AnaSubsume : ∀ {Γ e-all syn-all ana-all m-all m-consist} ->
        SubsumableMid e-all ->
        syn-all ~N ana-all , m-consist ->
        ▶ m-consist m-all ->
        Γ ⊢ (e-all ⇒ syn-all) ⇒ -> 
        Γ ⊢ ((e-all ⇒ syn-all) [ m-all ]⇐ ana-all) ⇐ 
      AnaFun : ∀ {Γ x e-body syn-all syn-body ana-all ana-body t-asc t-in-ana t-out-ana m-ana m-asc m-all m-body m-ana-ana m-asc-ana m-all-ana} ->
        -- analytic flow
        ana-all ▸NTArrow t-in-ana , t-out-ana , m-ana-ana -> 
        t-asc ■~N t-in-ana , m-asc-ana ->
        ▷ t-out-ana ana-body ->
        ▶ m-ana-ana m-ana -> 
        ▶ m-asc-ana m-asc -> 
        -- synthetic flow
        ▷ (NUnless (NArrow t-asc syn-body) ana-all) syn-all -> -- <-- this step also flows from ana
        syn-all ~N ana-all , m-all-ana ->
        ▶ m-all-ana m-all -> 
        -- recursive call
        (x ∶ t-asc ∷? Γ) ⊢ ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body) ⇐ ->
        Γ ⊢ (((EFun x t-asc m-ana m-asc ((e-body ⇒ syn-body) [ m-body ]⇐ ana-body)) ⇒ syn-all) [ m-all ]⇐ ana-all) ⇐  
      
  data WellTypedProgram : Program -> Set where 
    WTProg : ∀ {p} ->
      ∅ ⊢ (ExpLowOfProgram p) ⇐ ->
      WellTypedProgram p