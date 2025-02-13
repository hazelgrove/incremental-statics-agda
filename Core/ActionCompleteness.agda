
open import Data.List 
open import Data.Product hiding (map)

open import Prelude
open import Core.Core
open import Core.WellTyped
open import Core.VarsSynthesize
open import Core.Actions

module Core.ActionCompleteness where

  AB*StepActAppend : ∀{As1 As2 e e' e''} ->
    As1 , e AB↦* e' -> 
    As2 , e' AB↦* e'' ->
    (As1 ++ As2) , e AB↦* e'' 
  AB*StepActAppend (AB*StepAct x steps) step = AB*StepAct x (AB*StepActAppend steps step)
  AB*StepActAppend AB*StepDone step = step 

  action-construction :
    (e : BareExp) -> 
    ∃[ As ] As , BareEHole AB↦* e
  action-construction BareEHole = [] , AB*StepDone
  action-construction BareEConst = ((InsertConst , []) ∷ []) , (AB*StepAct (ABareDone ActInsertConst) AB*StepDone)
  action-construction (BareEVar x) = ((InsertVar x , []) ∷ []) , (AB*StepAct (ABareDone ActInsertVar) AB*StepDone)
  action-construction (BareEFun x t e) with action-construction e 
  ... | As , steps = As ∷ʳ (WrapFun x , []) ∷ʳ (SetAnn t , []) , (AB*StepActAppend (AB*StepActAppend steps (AB*StepAct (ABareDone ActWrapFun) AB*StepDone)) (AB*StepAct (ABareDone ActSetAnn) AB*StepDone))
  action-construction (BareEAsc t e) with action-construction e 
  ... | As , steps = As ∷ʳ (WrapAsc , []) ∷ʳ (SetAsc t , []) , (AB*StepActAppend (AB*StepActAppend steps (AB*StepAct (ABareDone ActWrapAsc) AB*StepDone)) (AB*StepAct (ABareDone ActSetAsc) AB*StepDone))
  action-construction (BareEAp e1 e2) with action-construction e1 | action-construction e2
  ... | As1 , steps1 | As2 , steps2 = (As1 ++ [ (WrapAp One , []) ] ++ map nest-action As2) , 
    AB*StepActAppend steps1 (AB*StepAct (ABareDone ActWrapApOne) (construct-helper steps2))
    where 
    nest-action : LocalizedAction -> LocalizedAction 
    nest-action (α , locale) = (α , Two ∷ locale)

    construct-helper : ∀{As2 e} ->
      As2 , e AB↦* e2 ->
      map nest-action As2 , BareEAp e1 e AB↦* BareEAp e1 e2
    construct-helper (AB*StepAct x steps) = AB*StepAct (ABareApTwo x) (construct-helper steps)
    construct-helper AB*StepDone = AB*StepDone
 
  action-completeness :
    (e1 e2 : BareExp) -> 
    ∃[ As ] As , e1 AB↦* e2
  action-completeness e1 e2 with action-construction e2   
  ... | As , steps = ((Delete , []) ∷ As) , AB*StepAct (ABareDone ActDelete) steps