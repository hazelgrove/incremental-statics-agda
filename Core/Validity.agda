open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.WellTyped
open import Core.Settled
open import Core.Marking

module Core.Validity where


validity : ∀ {e b t} ->
  -- e well typed 
  Settled e ->
  BarrenExp e b ->
  ∅ ⊢ b ~> e ⇒ t