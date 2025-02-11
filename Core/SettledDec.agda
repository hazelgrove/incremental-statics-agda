
open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Settled

module Core.SettledDec where

  mutual 

    settled-dec-up : 
      (e : ExpUp) -> 
      (e U̸↦) + ¬(e U̸↦)
    settled-dec-up (EConst ⇒ (_ , New)) = Inr λ ()
    settled-dec-up (EConst ⇒ (_ , Old)) = Inl (SettledUp SettledConst)
    settled-dec-up (EHole ⇒ (_ , New)) = Inr λ ()
    settled-dec-up (EHole ⇒ (_ , Old)) =  Inl (SettledUp SettledHole)
    settled-dec-up (EVar _ _ ⇒ (_ , New)) = Inr λ ()
    settled-dec-up (EVar _ _ ⇒ (_ , Old)) = Inl (SettledUp SettledVar)
    settled-dec-up (EFun x t m1 m2 e ⇒ (syn , New)) = Inr λ ()
    settled-dec-up (EFun x (t , New) m1 m2 e ⇒ (syn , Old)) = Inr helper
      where 
      helper : ¬ (EFun x (t , New) m1 m2 e ⇒ (syn , Old)) U̸↦
      helper (SettledUp ()) 
    settled-dec-up (EFun x (t , Old) m1 m2 e ⇒ (syn , Old)) with settled-dec-low e 
    ... | Inl settled = Inl (SettledUp (SettledFun settled))
    ... | Inr unsettled = Inr helper
      where 
      helper : ¬ (EFun x (t , Old) m1 m2 e ⇒ (syn , Old)) U̸↦
      helper (SettledUp (SettledFun settled)) = unsettled settled 
    settled-dec-up (EAsc _ _ ⇒ (syn , New)) = Inr λ ()
    settled-dec-up (EAsc (t , New) e ⇒ (syn , Old)) = Inr helper
      where 
      helper : ¬ (EAsc (t , New) e ⇒ (syn , Old)) U̸↦
      helper (SettledUp ()) 
    settled-dec-up (EAsc (t , Old) e ⇒ (syn , Old)) with settled-dec-low e 
    ... | Inl settled = Inl (SettledUp (SettledAsc settled))
    ... | Inr unsettled = Inr helper
      where 
      helper : ¬ (EAsc (t , Old) e ⇒ (syn , Old)) U̸↦
      helper (SettledUp (SettledAsc settled)) = unsettled settled 
    settled-dec-up (EAp e1 _ e2 ⇒ (t , New)) = Inr λ ()
    settled-dec-up (EAp e1 m e2 ⇒ (t , Old)) with settled-dec-low e1 | settled-dec-low e2 
    ... | Inr unsettled | _ = Inr helper
      where 
      helper : ¬ (EAp e1 m e2 ⇒ (t , Old)) U̸↦
      helper (SettledUp (SettledAp settled _)) = unsettled settled 
    ... | Inl settled1 | Inr unsettled = Inr helper
      where 
      helper : ¬ (EAp e1 m e2 ⇒ (t , Old)) U̸↦
      helper (SettledUp (SettledAp _ settled)) = unsettled settled 
    ... | Inl settled1 | Inl settled2 = Inl (SettledUp (SettledAp settled1 settled2))

    settled-dec-low : 
      (e : ExpLow) -> 
      (e L̸↦) + ¬(e L̸↦)
    settled-dec-low (e [ m ]⇐ (t , New)) = Inr λ ()
    settled-dec-low (e [ m ]⇐ (t , Old)) with settled-dec-up e 
    ... | Inr unsettled = Inr helper
      where 
      helper : ¬ (e [ m ]⇐ (t , Old)) L̸↦
      helper (SettledLow settled) = unsettled settled 
    ... | Inl settled = Inl (SettledLow settled)

  settled-dec : (p : Program) -> 
    (p P̸↦) + ¬(p P̸↦)
  settled-dec p with settled-dec-low (ExpLowOfProgram p)
  ... | Inl settled = Inl (SettledProgram settled)
  ... | Inr unsettled = Inr λ settled → unsettled (helper settled)
    where 
    helper : (p P̸↦) -> (ExpLowOfProgram p) L̸↦
    helper (SettledProgram settled) = settled
  