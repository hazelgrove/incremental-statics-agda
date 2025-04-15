
open import Data.Product
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core

module Core.TypVariableUpdate where

  data TypVariableUpdate : Var -> Mark -> Type -> Type -> Set where 
    TVUBase : ∀ {x m} ->
      TypVariableUpdate x m TBase TBase
    TVUHole : ∀ {x m} ->
      TypVariableUpdate x m THole THole
    TVUArrow : ∀ {x m t1 t2 t3 t4} ->
      TypVariableUpdate x m t1 t3 ->
      TypVariableUpdate x m t2 t4 ->
      TypVariableUpdate x m (TArrow t1 t2) (TArrow t3 t4)
    TVUProd : ∀ {x m t1 t2 t3 t4} ->
      TypVariableUpdate x m t1 t3 ->
      TypVariableUpdate x m t2 t4 ->
      TypVariableUpdate x m (TProd t1 t2) (TProd t3 t4)
    TVUVarEq : ∀ {x m m'} ->
      TypVariableUpdate x m (TVar x m') (TVar x m)
    TVUVarNeq : ∀ {x m x' m'} ->
      ¬(x' ≡ x) -> 
      TypVariableUpdate x m (TVar x' m') (TVar x' m')
    TVUForallEq : ∀ {x m t} ->
      TypVariableUpdate x m (TForall (BVar x) t) (TForall (BVar x) t)
    TVUForallNeq : ∀ {x m x' t t'} ->
      ¬((BVar x) ≡ x') ->
      TypVariableUpdate x m t t' ->
      TypVariableUpdate x m (TForall x' t) (TForall x' t')
    
  TypVariableUpdate? : Binding -> Mark -> Type -> Type -> Set
  TypVariableUpdate? BHole m t1 t2 = t1 ≡ t2
  TypVariableUpdate? (BVar x) m t1 t2 = TypVariableUpdate x m t1 t2

  data ExpTypVariableUpdate : Var -> Mark -> SynExp -> SynExp -> Set where 
    ETVUConst : ∀ {x m syn} ->
      ExpTypVariableUpdate x m (EConst ⇒ syn) (EConst ⇒ syn)
    ETVUHole : ∀ {x m syn} ->
      ExpTypVariableUpdate x m (EHole ⇒ syn) (EHole ⇒ syn)
    ETVUFun : ∀ {x m x' ann ann' n-ann m-ana m-asc e-body e-body' m-body syn-all ana-body} ->
      TypVariableUpdate x m ann ann' ->
      ExpTypVariableUpdate x m e-body e-body' ->
      ExpTypVariableUpdate x m ((EFun x' (ann , n-ann) m-ana m-asc (e-body [ m-body ]⇐ ana-body)) ⇒ syn-all) ((EFun x' (ann , ★) m-ana m-asc (e-body' [ m-body ]⇐ ana-body)) ⇒ syn-all)
    ETVUAp : ∀ {x m syn e1 e2 e1' e2' ana1 ana2 m1 m2 m3} ->
      ExpTypVariableUpdate x m e1 e1' ->
      ExpTypVariableUpdate x m e2 e2' ->
      ExpTypVariableUpdate x m ((EAp (e1 [ m1 ]⇐ ana1) m2 (e2 [ m3 ]⇐ ana2)) ⇒ syn) ((EAp (e1' [ m1 ]⇐ ana1) m2 (e2' [ m3 ]⇐ ana2)) ⇒ syn)
    ETVUVar : ∀ {x m x' m' syn} ->
      ExpTypVariableUpdate x m ((EVar x' m') ⇒ syn) ((EVar x' m') ⇒ syn)
    ETVUAsc : ∀ {x m syn asc asc' n-asc e e' ana m'} ->
      TypVariableUpdate x m asc asc' ->
      ExpTypVariableUpdate x m e e' ->
      ExpTypVariableUpdate x m ((EAsc (asc , n-asc) (e [ m' ]⇐ ana)) ⇒ syn) ((EAsc (asc' , ★) (e' [ m' ]⇐ ana)) ⇒ syn)
    ETVUPair : ∀ {x m syn e1 e1' e2 e2' ana1 ana2 m1 m2 m'} ->
      ExpTypVariableUpdate x m e1 e1' ->
      ExpTypVariableUpdate x m e2 e2' ->
      ExpTypVariableUpdate x m ((EPair (e1 [ m1 ]⇐ ana1) (e2 [ m2 ]⇐ ana2) m') ⇒ syn) ((EPair (e1' [ m1 ]⇐ ana1) (e2' [ m2 ]⇐ ana2) m') ⇒ syn) 
    ETVUProj : ∀ {x s m syn e e' ana m' m''} ->
      ExpTypVariableUpdate x m e e' ->
      ExpTypVariableUpdate x m ((EProj s (e [ m' ]⇐ ana) m'') ⇒ syn) ((EProj s (e' [ m' ]⇐ ana) m'') ⇒ syn) 
    ETVUTypFunEq : ∀ {x syn e ana m m' m''} ->
      ExpTypVariableUpdate x m ((ETypFun (BVar x) m' (e [ m'' ]⇐ ana)) ⇒ syn) ((ETypFun (BVar x) m' (e [ m'' ]⇐ ana)) ⇒ syn) 
    ETVUTypFunNeq : ∀ {x x' m syn e e' ana m' m''} ->
      ¬((BVar x) ≡ x') ->
      ExpTypVariableUpdate x m e e' ->
      ExpTypVariableUpdate x m ((ETypFun x' m' (e [ m'' ]⇐ ana)) ⇒ syn) ((ETypFun x' m' (e' [ m'' ]⇐ ana)) ⇒ syn) 
    ETVUTypAp : ∀ {x m syn t t' n e e' ana m' m''} ->
      ExpTypVariableUpdate x m e e' ->
      TypVariableUpdate x m t t' ->
      ExpTypVariableUpdate x m ((ETypAp (e [ m' ]⇐ ana) m'' (t , n)) ⇒ syn) ((ETypAp (e' [ m' ]⇐ ana) m'' (t' , ★)) ⇒ syn)

  ExpTypVariableUpdate? : Binding -> Mark -> SynExp -> SynExp -> Set
  ExpTypVariableUpdate? BHole m e1 e2 = e1 ≡ e2
  ExpTypVariableUpdate? (BVar x) m e1 e2 = ExpTypVariableUpdate x m e1 e2 