 
open import Data.Empty 
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.WellTyped
open import Core.VarsSynthesize
open import Core.Lemmas

module Core.VarsSynthesizePreservation where

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
    ctx-inv-ana equiv (WTUp x x₁ x₂ x₃) = WTUp x x₁ x₂ (ctx-inv-syn equiv x₃)
    ctx-inv-ana equiv (WTFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = WTFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ (ctx-inv-ana (CtxEquivCons? equiv) ana)

    ctx-inv-syn : ∀ {Γ Γ' e} ->
      CtxEquiv Γ Γ' ->
      Γ U⊢ e ->
      Γ' U⊢ e
    ctx-inv-syn equiv (WTConst x) = WTConst x
    ctx-inv-syn equiv (WTHole x) = WTHole x
    ctx-inv-syn equiv (WTAp x x₁ x₂ x₃ x₄ x₅) = WTAp x x₁ x₂ x₃ (ctx-inv-ana equiv x₄) (ctx-inv-ana equiv x₅)
    ctx-inv-syn equiv (WTVar x x₁) = WTVar (ctx-equiv-access equiv x) x₁
    ctx-inv-syn equiv (WTAsc x x₁ x₂) = WTAsc x x₁ (ctx-inv-ana equiv x₂)

  mutual 

    preservation-vars-ana :
      ∀ {Γ Γ' x t m' e e' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      VarsSynthesize x t ✔ e e' ->
      CtxInv x t Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-vars-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (WTUp subsumable consist-t consist-m syn) vars-syn ctx-inv with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = WTUp (vars-syn-subsumable vars-syn subsumable) consist-t' (beyond-▶ (beyond-through-~N (vars-syn-beyond vars-syn) consist-t consist-t') consist-m) (preservation-vars-syn syn vars-syn ctx-inv)
    preservation-vars-ana (WTFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunNeq {e-body' = e-body' ⇒ syn-body'} neq vars-syn) ctx-inv = WTFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma {t = t-asc} (vars-syn?-beyond vars-syn) consist-syn) consist-all consist-m-all (preservation-vars-ana ana vars-syn (CtxInvNeq? neq ctx-inv))    
    preservation-vars-ana (WTFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunEq) ctx-inv = WTFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all (ctx-inv-ana (CtxEquivInit ctx-inv) ana)

    preservation-vars-syn :
      ∀ {Γ Γ' x t e e'} ->
      Γ U⊢ e ->
      VarsSynthesize x t ✔ e e' ->
      CtxInv x t Γ Γ' ->
      Γ' U⊢ e'
    preservation-vars-syn (WTConst consist) VSConst ctx-inv = WTConst consist
    preservation-vars-syn (WTHole consist) VSHole ctx-inv = WTHole consist
    preservation-vars-syn (WTAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} vars-syn-fun vars-syn-arg) ctx-inv with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (vars-syn-beyond vars-syn-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = WTAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-ana syn vars-syn-fun ctx-inv) (preservation-vars-ana ana vars-syn-arg ctx-inv)
    preservation-vars-syn {t = t} (WTVar in-ctx consist) VSVarEq ctx-inv = WTVar (ctx-inv-access-eq ctx-inv) (▷Pair ▶Old) 
    preservation-vars-syn (WTVar in-ctx consist) (VSVarNeq neq) ctx-inv = WTVar (ctx-inv-access-neq ctx-inv (λ eq → neq (sym eq)) in-ctx) consist
    preservation-vars-syn (WTAsc consist-syn consist-ana ana) (VSAsc vars-syn) ctx-inv = WTAsc consist-syn consist-ana (preservation-vars-ana ana vars-syn ctx-inv)

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
    preservation-vars-unwrap-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (WTUp subsumable consist-t consist-m syn) vars-syn ctx-inv with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = WTUp (vars-syn-subsumable vars-syn subsumable) consist-t' (beyond-▶ (beyond-through-~N (vars-syn-beyond vars-syn) consist-t consist-t') consist-m) (preservation-vars-unwrap-syn syn vars-syn ctx-inv)
    preservation-vars-unwrap-ana (WTFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunNeq {e-body' = e-body' ⇒ syn-body'} neq vars-syn) ctx-inv = WTFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma {t = t-asc} (vars-syn?-beyond vars-syn) consist-syn) consist-all consist-m-all (preservation-vars-unwrap-ana ana vars-syn (UnwrapInvCons? neq ctx-inv))    
    preservation-vars-unwrap-ana (WTFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunEq) ctx-inv = WTFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all (ctx-inv-ana (CtxEquivUnwrapInit ctx-inv) ana)

    preservation-vars-unwrap-syn :
      ∀ {Γ Γ' x t m e e'} ->
      Γ U⊢ e ->
      VarsSynthesize x t m e e' ->
      UnwrapInv x t m Γ Γ' ->
      Γ' U⊢ e'
    preservation-vars-unwrap-syn (WTConst consist) VSConst ctx-inv = WTConst consist
    preservation-vars-unwrap-syn (WTHole consist) VSHole ctx-inv = WTHole consist
    preservation-vars-unwrap-syn (WTAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} vars-syn-fun vars-syn-arg) ctx-inv with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (vars-syn-beyond vars-syn-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = WTAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-unwrap-ana syn vars-syn-fun ctx-inv) (preservation-vars-unwrap-ana ana vars-syn-arg ctx-inv)
    preservation-vars-unwrap-syn {t = t} (WTVar in-ctx consist) VSVarEq ctx-inv = WTVar (proj₂ (unwrap-inv-access-eq ctx-inv)) (▷Pair ▶Same)
    preservation-vars-unwrap-syn (WTVar in-ctx consist) (VSVarNeq neq) ctx-inv = WTVar (unwrap-inv-access-neq ctx-inv neq in-ctx) consist
    preservation-vars-unwrap-syn (WTAsc consist-syn consist-ana ana) (VSAsc vars-syn) ctx-inv = WTAsc consist-syn consist-ana (preservation-vars-unwrap-ana ana vars-syn ctx-inv)

  preservation-vars-unwrap : 
    ∀ {x Γ t t-old e e' m m' ana n} ->
    (x , (t , n) ∈N? Γ , m) -> 
    (x ∶ t-old ∷? Γ) L⊢ (e [ m' ]⇐ ana) ->
    VarsSynthesize? x t m e e' ->
    Γ L⊢ (e' [ m' ]⇐ ana)
  preservation-vars-unwrap {BHole} in-ctx ana refl = ana
  preservation-vars-unwrap {BVar x} in-ctx ana vars-syn = preservation-vars-unwrap-ana ana vars-syn (UnwrapInvInit in-ctx)