open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.WellTyped

module Core.Environment where

  mutual 

    data LEnvUp : Set where 
      LEnvUpRec : LEnvMid -> NewData -> LEnvUp

    data LEnvMid : Set where 
      LEnvFun : Binding -> NewType -> Mark -> Mark -> LEnvLow -> LEnvMid 
      LEnvAp1 : LEnvLow -> Mark -> ExpLow -> LEnvMid 
      LEnvAp2 : ExpLow -> Mark -> LEnvLow -> LEnvMid 
      LEnvAsc : NewType -> LEnvLow -> LEnvMid 

    data LEnvLow : Set where 
      L⊙ : LEnvLow
      LEnvLowRec : LEnvUp -> Mark -> NewData -> LEnvLow

  mutual 

    data UEnvUp : Set where 
      U⊙ : UEnvUp
      UEnvUpRec : UEnvMid -> NewData -> UEnvUp

    data UEnvMid : Set where 
      UEnvFun : Binding -> NewType -> Mark -> Mark -> UEnvLow -> UEnvMid 
      UEnvAp1 : UEnvLow -> Mark -> ExpLow -> UEnvMid 
      UEnvAp2 : ExpLow -> Mark -> UEnvLow -> UEnvMid 
      UEnvAsc : NewType -> UEnvLow -> UEnvMid 

    data UEnvLow : Set where 
      UEnvLowRec : UEnvUp -> Mark -> NewData -> UEnvLow

  mutual 
    data _L⟦_⟧Up==_ : (ε : LEnvUp) (e : ExpLow) (e' : ExpUp)  -> Set where
      FillLEnvUpRec : ∀ {e ε e' syn} ->
        ε L⟦ e ⟧Mid== e' ->
        (LEnvUpRec ε syn) L⟦ e ⟧Up== (e' ⇒ syn)

    data _L⟦_⟧Mid==_ : (ε : LEnvMid) (e : ExpLow) (e' : ExpMid)  -> Set where
      FillLEnvFun : ∀ {e ε e' x t m1 m2} ->
        ε L⟦ e ⟧Low== e' ->
        (LEnvFun x t m1 m2 ε) L⟦ e ⟧Mid== (EFun x t m1 m2 e')
      FillLEnvAp1 : ∀ {e ε e' e2 m} ->
        ε L⟦ e ⟧Low== e' ->
        (LEnvAp1 ε m e2) L⟦ e ⟧Mid== (EAp e' m e2)
      FillLEnvAp2 : ∀ {e ε e' e1 m} ->
        ε L⟦ e ⟧Low== e' ->
        (LEnvAp2 e1 m ε) L⟦ e ⟧Mid== (EAp e1 m e')
      FillLEnvAsc : ∀ {e ε e' t} ->
        ε L⟦ e ⟧Low== e' ->
        (LEnvAsc t ε) L⟦ e ⟧Mid== (EAsc t e')

    data _L⟦_⟧Low==_ : (ε : LEnvLow) (e : ExpLow) (e' : ExpLow)  -> Set where
      FillL⊙ : ∀ {e} ->
        L⊙ L⟦ e ⟧Low== e
      FillLEnvLowRec : ∀ {e e' ana m ε} ->
        ε L⟦ e ⟧Up== e' ->
        LEnvLowRec ε m ana L⟦ e ⟧Low== (e' [ m ]⇐ ana)

  mutual 
    data _U⟦_⟧Up==_ : (ε : UEnvUp) (e : ExpUp) (e' : ExpUp)  -> Set where
      FillU⊙ : ∀ {e} ->
        U⊙ U⟦ e ⟧Up== e
      FillUEnvUpRec : ∀ {e ε e' syn} ->
        ε U⟦ e ⟧Mid== e' ->
        (UEnvUpRec ε syn) U⟦ e ⟧Up== (e' ⇒ syn)

    data _U⟦_⟧Mid==_ : (ε : UEnvMid) (e : ExpUp) (e' : ExpMid)  -> Set where
      FillUEnvFun : ∀ {e ε e' x t m1 m2} ->
        ε U⟦ e ⟧Low== e' ->
        (UEnvFun x t m1 m2 ε) U⟦ e ⟧Mid== (EFun x t m1 m2 e')
      FillUEnvAp1 : ∀ {e ε e' e2 m} ->
        ε U⟦ e ⟧Low== e' ->
        (UEnvAp1 ε m e2) U⟦ e ⟧Mid== (EAp e' m e2)
      FillUEnvAp2 : ∀ {e ε e' e1 m} ->
        ε U⟦ e ⟧Low== e' ->
        (UEnvAp2 e1 m ε) U⟦ e ⟧Mid== (EAp e1 m e')
      FillUEnvAsc : ∀ {e ε e' t} ->
        ε U⟦ e ⟧Low== e' ->
        (UEnvAsc t ε) U⟦ e ⟧Mid== (EAsc t e')

    data _U⟦_⟧Low==_ : (ε : UEnvLow) (e : ExpUp) (e' : ExpLow)  -> Set where
      FillUEnvLowRec : ∀ {e e' ana m ε} ->
        ε U⟦ e ⟧Up== e' ->
        UEnvLowRec ε m ana U⟦ e ⟧Low== (e' [ m ]⇐ ana)