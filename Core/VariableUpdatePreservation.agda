 
open import Data.Empty 
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.WellFormed
open import Core.VariableUpdate
open import Core.Lemmas

module Core.VariableUpdatePreservation where

  var-update-subsumable : ∀ {x t m e e' syn syn'} ->
    VariableUpdate x t m (e ⇒ syn) (e' ⇒ syn') -> 
    SubsumableMid e ->
    SubsumableMid e'
  var-update-subsumable VSConst SubsumableConst = SubsumableConst
  var-update-subsumable VSHole SubsumableHole = SubsumableHole
  var-update-subsumable VSFunEq ()
  var-update-subsumable (VSFunNeq neq var-update) ()
  var-update-subsumable (VSAp var-update1 var-update2) SubsumableAp = SubsumableAp
  var-update-subsumable VSVarEq SubsumableVar = SubsumableVar
  var-update-subsumable (VSVarNeq _) SubsumableVar = SubsumableVar
  var-update-subsumable (VSAsc var-update) SubsumableAsc = SubsumableAsc
  var-update-subsumable (VSProj var-update) SubsumableProj = SubsumableProj

  var-update-beyond : ∀ {x t m e syn e' syn'} ->
    VariableUpdate x t m (e ⇒ syn) (e' ⇒ syn') -> 
    =▷ syn syn' 
  var-update-beyond VSConst = =▷Refl
  var-update-beyond VSHole = =▷Refl
  var-update-beyond VSFunEq = =▷Refl
  var-update-beyond (VSFunNeq neq syn) = =▷Refl
  var-update-beyond (VSAp syn syn₁) = =▷Refl
  var-update-beyond VSVarEq = =▷★
  var-update-beyond (VSVarNeq x) = =▷Refl
  var-update-beyond (VSAsc syn) = =▷Refl
  var-update-beyond (VSPair syn syn₁) = =▷Refl
  var-update-beyond (VSProj syn) = =▷Refl

  var-update?-beyond : ∀ {x t m e syn e' syn'} ->
    VariableUpdate? x t m (e ⇒ syn) (e' ⇒ syn') -> 
    =▷ syn syn' 
  var-update?-beyond {BHole} refl = =▷Refl
  var-update?-beyond {BVar x} var-update = var-update-beyond var-update

  data CtxInv : Var -> Type -> Dirtiness -> Ctx -> Ctx -> Set where 
    CtxInvInit : ∀ {Γ x t n} ->
      CtxInv x t n Γ (x ∶ t , n ∷ Γ)
    CtxInvInit2 : ∀ {Γ x t n} ->
      CtxInv x t n (x ∶ t , ★ ∷ Γ) (x ∶ t , n ∷ Γ)
    CtxInvNeq : ∀ {x x' n t t' Γ Γ'} ->
      ¬(x ≡ x') ->
      CtxInv x t n Γ Γ' ->
      CtxInv x t n (x' ∶ t' ∷ Γ) (x' ∶ t' ∷ Γ')

  CtxInvNeq? : ∀ {x' x t t' n Γ Γ'} ->
    ¬(BVar x ≡ x') ->
    CtxInv x t n Γ Γ' ->
    CtxInv x t n (x' ∶ t' ∷? Γ) (x' ∶ t' ∷? Γ')
  CtxInvNeq? {BHole} neq inv = inv
  CtxInvNeq? {BVar x} neq inv = CtxInvNeq (λ eq → neq (cong BVar eq)) inv

  ctx-inv-access-eq : ∀ {x t n Γ Γ'} ->
    CtxInv x t n Γ Γ' ->
    x , (t , n) ∈N Γ' , ✔
  ctx-inv-access-eq CtxInvInit = InCtxFound
  ctx-inv-access-eq CtxInvInit2 = InCtxFound
  ctx-inv-access-eq (CtxInvNeq neq inv) = InCtxSkip neq (ctx-inv-access-eq inv)

  ctx-inv-access-neq : ∀ {x x' t t' n m Γ Γ'} ->
    CtxInv x t n Γ Γ' ->
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
    CtxEquivInit : ∀ {x t t' n Γ Γ'} ->
      CtxInv x t n Γ Γ' ->
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
    ctx-inv-ana equiv (WFSubsume x x₁ x₂ x₃) = WFSubsume x x₁ x₂ (ctx-inv-syn equiv x₃)
    ctx-inv-ana equiv (WFFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ ana) = WFFun x x₁ x₂ x₃ x₄ x₅ x₆ x₇ (ctx-inv-ana (CtxEquivCons? equiv) ana)
    ctx-inv-ana equiv (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (ctx-inv-ana equiv wt) (ctx-inv-ana equiv wt₁)

    ctx-inv-syn : ∀ {Γ Γ' e} ->
      CtxEquiv Γ Γ' ->
      Γ S⊢ e ->
      Γ' S⊢ e
    ctx-inv-syn equiv (WFConst x) = WFConst x
    ctx-inv-syn equiv (WFHole x) = WFHole x
    ctx-inv-syn equiv (WFAp x x₁ x₂ x₃ x₄ x₅) = WFAp x x₁ x₂ x₃ (ctx-inv-ana equiv x₄) (ctx-inv-ana equiv x₅)
    ctx-inv-syn equiv (WFVar x x₁) = WFVar (ctx-equiv-access equiv x) x₁
    ctx-inv-syn equiv (WFAsc x x₁ x₂) = WFAsc x x₁ (ctx-inv-ana equiv x₂)
    ctx-inv-syn equiv (WFProj x x₁ x₂ x₃) = WFProj x x₁ x₂ (ctx-inv-ana equiv x₃)

  mutual 

    preservation-vars-ana :
      ∀ {Γ Γ' x t n m' e e' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      VariableUpdate x t ✔ e e' ->
      CtxInv x t n Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-vars-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (WFSubsume subsumable consist-t consist-m syn) var-update ctx-inv with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = WFSubsume (var-update-subsumable var-update subsumable) consist-t' (beyond-▶ (beyond-through-~N (var-update-beyond var-update) consist-t consist-t') consist-m) (preservation-var-update syn var-update ctx-inv)
    preservation-vars-ana (WFFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunNeq {e-body' = e-body' ⇒ syn-body'} neq var-update) ctx-inv = WFFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma {t = t-asc} (var-update?-beyond var-update) consist-syn) consist-all consist-m-all (preservation-vars-ana ana var-update (CtxInvNeq? neq ctx-inv))    
    preservation-vars-ana (WFFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunEq) ctx-inv = WFFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all (ctx-inv-ana (CtxEquivInit ctx-inv) ana)
    preservation-vars-ana (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (VSPair {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} vs vs₁) ctx-inv = WFPair x x₁ x₂ x₃ (preservation-pair-lemma (var-update?-beyond vs) (var-update?-beyond vs₁) x₄) x₅ x₆ (preservation-vars-ana wt vs ctx-inv) (preservation-vars-ana wt₁ vs₁ ctx-inv)

    preservation-var-update :
      ∀ {Γ Γ' x t n e e'} ->
      Γ S⊢ e ->
      VariableUpdate x t ✔ e e' ->
      CtxInv x t n Γ Γ' ->
      Γ' S⊢ e'
    preservation-var-update (WFConst consist) VSConst ctx-inv = WFConst consist
    preservation-var-update (WFHole consist) VSHole ctx-inv = WFHole consist
    preservation-var-update (WFAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} var-update-fun var-update-arg) ctx-inv with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (var-update-beyond var-update-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = WFAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-ana syn var-update-fun ctx-inv) (preservation-vars-ana ana var-update-arg ctx-inv)
    preservation-var-update {t = t} (WFVar in-ctx consist) VSVarEq ctx-inv = WFVar (ctx-inv-access-eq ctx-inv) (▷Pair ▶Same)
    preservation-var-update (WFVar in-ctx consist) (VSVarNeq neq) ctx-inv = WFVar (ctx-inv-access-neq ctx-inv (λ eq → neq (sym eq)) in-ctx) consist
    preservation-var-update (WFAsc consist-syn consist-ana ana) (VSAsc var-update) ctx-inv = WFAsc consist-syn consist-ana (preservation-vars-ana ana var-update ctx-inv)
    preservation-var-update (WFProj {s = s} mprod x₁ x₂ x₃) (VSProj {e' = e-body' ⇒ syn-body'} vs) ctx-inv with ▸NTProj-dec s syn-body' 
    ... | t-side-body' , m-body' , mprod' with beyond-▸NTProj (var-update-beyond vs) mprod mprod' 
    ... | t-beyond , m-beyond = WFProj mprod' (beyond-▷ t-beyond x₁) (beyond-▶ m-beyond x₂) (preservation-vars-ana x₃ vs ctx-inv)

  preservation-vars-ana? :
    ∀ {x Γ t e e' n m' ana} ->
    Γ L⊢ (e [ m' ]⇐ ana) ->
    VariableUpdate? x t ✔ e e' ->
    (x ∶ t , n ∷? Γ) L⊢ (e' [ m' ]⇐ ana)
  preservation-vars-ana? {BHole} ana refl = ana
  preservation-vars-ana? {BVar x} ana var-update = preservation-vars-ana ana var-update CtxInvInit

  preservation-vars-ana?-step :
    ∀ {x Γ t e e' m' ana} ->
    (x ∶ t , ★ ∷? Γ) L⊢ (e [ m' ]⇐ ana) ->
    VariableUpdate? x t ✔ e e' ->
    (x ∶ t , • ∷? Γ) L⊢ (e' [ m' ]⇐ ana)
  preservation-vars-ana?-step {BHole} ana refl = ana
  preservation-vars-ana?-step {BVar x} ana var-update = preservation-vars-ana ana var-update CtxInvInit2

  mutual 

    preservation-vars-unwrap-ana :
      ∀ {Γ Γ' x t m m' e e' ana} ->
      Γ L⊢ (e [ m' ]⇐ ana) ->
      VariableUpdate x t m e e' ->
      UnwrapInv x t m Γ Γ' ->
      Γ' L⊢ (e' [ m' ]⇐ ana)
    preservation-vars-unwrap-ana {e' = e-all' ⇒ syn-all'} {ana = ana} (WFSubsume subsumable consist-t consist-m syn) var-update ctx-inv with ~N-dec syn-all' ana 
    ... | m-consist' , consist-t' = WFSubsume (var-update-subsumable var-update subsumable) consist-t' (beyond-▶ (beyond-through-~N (var-update-beyond var-update) consist-t consist-t') consist-m) (preservation-vars-unwrap-syn syn var-update ctx-inv)
    preservation-vars-unwrap-ana (WFFun {t-asc = t-asc} marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunNeq {e-body' = e-body' ⇒ syn-body'} neq var-update) ctx-inv = WFFun marrow consist consist-ana consist-asc consist-body (preservation-lambda-lemma {t = t-asc} (var-update?-beyond var-update) consist-syn) consist-all consist-m-all (preservation-vars-unwrap-ana ana var-update (UnwrapInvCons? neq ctx-inv))    
    preservation-vars-unwrap-ana (WFFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) (VSFunEq) ctx-inv = WFFun marrow consist consist-ana consist-asc consist-body consist-syn consist-all consist-m-all (ctx-inv-ana (CtxEquivUnwrapInit ctx-inv) ana)
    preservation-vars-unwrap-ana (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) (VSPair {e1' = e1' ⇒ syn1'} {e2' = e2' ⇒ syn2'} vs vs₁) ctx-inv = WFPair x x₁ x₂ x₃ (preservation-pair-lemma (var-update?-beyond vs) (var-update?-beyond vs₁) x₄) x₅ x₆ (preservation-vars-unwrap-ana wt vs ctx-inv) (preservation-vars-unwrap-ana wt₁ vs₁ ctx-inv)

    preservation-vars-unwrap-syn :
      ∀ {Γ Γ' x t m e e'} ->
      Γ S⊢ e ->
      VariableUpdate x t m e e' ->
      UnwrapInv x t m Γ Γ' ->
      Γ' S⊢ e'
    preservation-vars-unwrap-syn (WFConst consist) VSConst ctx-inv = WFConst consist
    preservation-vars-unwrap-syn (WFHole consist) VSHole ctx-inv = WFHole consist
    preservation-vars-unwrap-syn (WFAp marrow consist-syn consist-ana consist-mark syn ana) (VSAp {e1' = e-fun' ⇒ syn-fun'} var-update-fun var-update-arg) ctx-inv with ▸NTArrow-dec syn-fun' 
    ... | t-in-fun' , t-out-fun' , m-fun' , marrow' with beyond-▸NTArrow (var-update-beyond var-update-fun) marrow marrow' 
    ... | t-in-beyond , t-out-beyond , m-beyond = WFAp marrow' (beyond-▷ t-out-beyond consist-syn) (beyond-▷ t-in-beyond consist-ana) (beyond-▶ m-beyond consist-mark) (preservation-vars-unwrap-ana syn var-update-fun ctx-inv) (preservation-vars-unwrap-ana ana var-update-arg ctx-inv)
    preservation-vars-unwrap-syn {t = t} (WFVar in-ctx consist) VSVarEq ctx-inv = WFVar (proj₂ (unwrap-inv-access-eq ctx-inv)) (▷Pair ▶Same)
    preservation-vars-unwrap-syn (WFVar in-ctx consist) (VSVarNeq neq) ctx-inv = WFVar (unwrap-inv-access-neq ctx-inv neq in-ctx) consist
    preservation-vars-unwrap-syn (WFAsc consist-syn consist-ana ana) (VSAsc var-update) ctx-inv = WFAsc consist-syn consist-ana (preservation-vars-unwrap-ana ana var-update ctx-inv)
    preservation-vars-unwrap-syn (WFProj {s = s} mprod x₁ x₂ x₃) (VSProj {e' = e-body' ⇒ syn-body'} vs) ctx-inv with ▸NTProj-dec s syn-body' 
    ... | t-side-body' , m-body' , mprod' with beyond-▸NTProj (var-update-beyond vs) mprod mprod' 
    ... | t-beyond , m-beyond = WFProj mprod' (beyond-▷ t-beyond x₁) (beyond-▶ m-beyond x₂) (preservation-vars-unwrap-ana x₃ vs ctx-inv)
    
  preservation-vars-unwrap : 
    ∀ {x Γ t t-old e e' m m' ana n} ->
    (x , (t , n) ∈N? Γ , m) -> 
    (x ∶ t-old ∷? Γ) L⊢ (e [ m' ]⇐ ana) ->
    VariableUpdate? x t m e e' ->
    Γ L⊢ (e' [ m' ]⇐ ana)
  preservation-vars-unwrap {BHole} in-ctx ana refl = ana 
  preservation-vars-unwrap {BVar x} in-ctx ana var-update = preservation-vars-unwrap-ana ana var-update (UnwrapInvInit in-ctx) 