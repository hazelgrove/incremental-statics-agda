open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.Settled where

data Settled : ExpUp -> Set where 
  SettledConst : ∀ {t} ->
    Settled (EUp (⇑ (t , Old)) EConst)
  SettledHole : ∀ {t} ->
    Settled (EUp (⇑ (t , Old)) EHole)
  SettledFunSyn : ∀ {t1 t2 m1 m2 e} ->
    Settled e ->
    Settled (EUp (⇑ (t1 , Old)) (EFun (t2 , Old) m1 (ELow ̸⇓ m2 e)))
  SettledFunAna : ∀ {t1 t2 m1 m2 e} ->
    Settled e ->
    Settled (EUp ̸⇑ (EFun (t1 , Old) m1 (ELow (⇓ (t2 , Old)) m2 e)))
  SettledAp : ∀ {t1 t2 m1 m2 m3 e1 e2} ->
    Settled e1 -> 
    Settled e2 -> 
    Settled (EUp (⇑ (t1 , Old)) (EAp (ELow ̸⇓ m1 e1) m2 (ELow (⇓ (t2 , Old)) m3 e2)))
  SettledVar : ∀ {t x m} ->
    Settled (EUp (⇑ (t , Old)) (EVar x m))
  SettledAsc : ∀ {t1 t2 t3 m e} ->
    Settled e -> 
    Settled (EUp (⇑ (t1 , Old)) (EAsc (t2 , Old) (ELow (⇓ (t3 , Old)) m e)))

data SettledExcept : ExpUp -> Set where 
  SettledExceptConst : ∀ {t n} ->
    SettledExcept (EUp (⇑ (t , n)) EConst)
  SettledExceptHole : ∀ {t n} ->
    SettledExcept (EUp (⇑ (t , n)) EHole)
  SettledExceptFunSyn : ∀ {t1 t2 m1 m2 e n} ->
    Settled e ->
    SettledExcept (EUp (⇑ (t1 , n)) (EFun (t2 , Old) m1 (ELow ̸⇓ m2 e)))
  SettledExceptFunAna : ∀ {t1 t2 m1 m2 e n} ->
    Settled e ->
    SettledExcept (EUp ̸⇑ (EFun (t1 , n) m1 (ELow (⇓ (t2 , Old)) m2 e)))
  SettledExceptAp : ∀ {t1 t2 m1 m2 m3 e1 e2 n} ->
    Settled e1 -> 
    Settled e2 -> 
    SettledExcept (EUp (⇑ (t1 , n)) (EAp (ELow ̸⇓ m1 e1) m2 (ELow (⇓ (t2 , Old)) m3 e2)))
  SettledExceptVar : ∀ {t x m n} ->
    SettledExcept (EUp (⇑ (t , n)) (EVar x m))
  SettledExceptAsc : ∀ {t1 t2 t3 m e n} ->
    Settled e -> 
    SettledExcept (EUp (⇑ (t1 , n)) (EAsc (t2 , Old) (ELow (⇓ (t3 , Old)) m e)))

data SettledLow : ExpLow -> Set where 
  SettledLowAna : ∀ {e t m} ->
    Settled e ->
    SettledLow (ELow (⇓ (t , Old)) m e)

data PSettled : Program -> Set where 
  PSettledRoot : ∀ {e} ->
    SettledExcept e -> 
    PSettled (PRoot e)

-- settled-implies-settled-except : ∀ {e} ->
--   (Settled e) -> (SettledExcept e)
-- settled-implies-settled-except SettledConst = SettledExceptConst
-- settled-implies-settled-except SettledHole = SettledExceptHole
-- settled-implies-settled-except SettledFunSyn = SettledExceptFunSyn
-- settled-implies-settled-except SettledFunAna = SettledExceptFunAna
-- settled-implies-settled-except (SettledAp s s₁) = SettledExceptAp s s₁
-- settled-implies-settled-except SettledVar = SettledExceptVar
-- settled-implies-settled-except (SettledAsc s) = SettledExceptAsc s


mutual 

  data SettledSyn : Ctx -> ExpUp -> Set where 
    SettledSynConst : ∀ {Γ t} ->
      SettledSyn Γ (EUp (⇑ (t , Old)) EConst)
    SettledSynHole : ∀ {Γ t} ->
      SettledSyn Γ (EUp (⇑ (t , Old)) EHole)
    SettledSynFun : ∀ {Γ t1 t2 m1 m2 e} ->
      SettledSyn ((t2 , Old) , Γ) e ->
      SettledSyn Γ (EUp (⇑ (t1 , Old)) (EFun (t2 , Old) m1 (ELow ̸⇓ m2 e)))
    SettledSynAp : ∀ {Γ t m1 m2 e1 e2} ->
      SettledSyn Γ e1 -> 
      SettledAna Γ e2 -> 
      SettledSyn Γ (EUp (⇑ (t , Old)) (EAp (ELow ̸⇓ m1 e1) m2 e2))
    SettledSynVar : ∀ {Γ t1 t2 x m} ->
      ((x , (t1 , Old) ∈ Γ) + (x ̸∈ Γ)) ->
      SettledSyn Γ (EUp (⇑ (t2 , Old)) (EVar x m))
    -- SettledSynVarFail : ∀ {Γ t x m} ->
    --   x ̸∈ Γ ->
    --   SettledSyn Γ (EUp (⇑ (t , Old)) (EVar x m))
    SettledSynAsc : ∀ {Γ t1 t2 e} ->
      SettledAna Γ e -> 
      SettledSyn Γ (EUp (⇑ (t1 , Old)) (EAsc (t2 , Old) e))

  data SettledAna : Ctx -> ExpLow -> Set where 
    SettledAnaFun : ∀ {Γ t1 t2 m1 m2 e} ->
      SettledAna Γ e ->
      SettledAna Γ (ELow (⇓ (t1 , Old)) m1 (EUp ̸⇑ (EFun (t2 , Old) m2 e)))
    SettledAnaSubsume : ∀ {Γ e t m} ->
      SettledSyn Γ e ->
      SettledAna Γ (ELow (⇓ (t , Old)) m e)


data SettledSynExcept : Ctx -> ExpUp -> Set where 
  SettledSynExceptConst : ∀ {Γ t n} ->
    SettledSynExcept Γ (EUp (⇑ (t , n)) EConst)
  SettledSynExceptHole : ∀ {Γ t n} ->
    SettledSynExcept Γ (EUp (⇑ (t , n)) EHole)
  SettledSynExceptFun : ∀ {Γ t1 t2 m1 m2 e n} ->
    SettledSyn ((t2 , Old) , Γ) e ->
    SettledSynExcept Γ (EUp (⇑ (t1 , n)) (EFun (t2 , Old) m1 (ELow ̸⇓ m2 e)))
  SettledSynExceptAp : ∀ {Γ t m1 m2 e1 e2 n} ->
    SettledSyn Γ e1 -> 
    SettledAna Γ e2 -> 
    SettledSynExcept Γ (EUp (⇑ (t , n)) (EAp (ELow ̸⇓ m1 e1) m2 e2))
  SettledSynExceptVar : ∀ {Γ t1 t2 x m n} ->
    ((x , (t1 , Old) ∈ Γ) + (x ̸∈ Γ)) ->
    SettledSynExcept Γ (EUp (⇑ (t2 , n)) (EVar x m))
  -- SettledSynExceptVarFail : ∀ {Γ t x m} ->
  --   x ̸∈ Γ ->
  --   SettledSynExcept Γ (EUp (⇑ (t , Old)) (EVar x m))
  SettledSynExceptAsc : ∀ {Γ t1 t2 e n} ->
    SettledAna Γ e -> 
    SettledSynExcept Γ (EUp (⇑ (t1 , n)) (EAsc (t2 , Old) e))