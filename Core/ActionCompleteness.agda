
open import Data.List 
open import Data.Product hiding (map)

open import Prelude
open import Core.Core
open import Core.WellFormed
open import Core.VariableUpdate
open import Core.Actions

module Core.ActionCompleteness where

  ABT*StepActAppend : ∀{As1 As2 e e' e''} ->
    As1 , e ABT↦* e' -> 
    As2 , e' ABT↦* e'' ->
    (As1 ++ As2) , e ABT↦* e'' 
  ABT*StepActAppend (ABT*StepAct x steps) step = ABT*StepAct x (ABT*StepActAppend steps step)
  ABT*StepActAppend ABT*StepDone step = step 
  
  nest-action : LocalizedAction -> LocalizedAction 
  nest-action (α , locale) = (α , Two ∷ locale)

  nest-action-one : LocalizedAction -> LocalizedAction 
  nest-action-one (α , locale) = (α , One ∷ locale)
  
  act-in-arrow : ∀{As2 e1 e2 e} ->
    As2 , e ABT↦* e2 ->
    map nest-action As2 , BareTArrow e1 e ABT↦* BareTArrow e1 e2
  act-in-arrow (ABT*StepAct x steps) = ABT*StepAct (ABareArrowTwo x) (act-in-arrow steps)
  act-in-arrow ABT*StepDone = ABT*StepDone

  act-in-prod : ∀{As2 e1 e2 e} ->
    As2 , e ABT↦* e2 ->
    map nest-action As2 , BareTProd e1 e ABT↦* BareTProd e1 e2
  act-in-prod (ABT*StepAct x steps) = ABT*StepAct (ABareProdTwo x) (act-in-prod steps)
  act-in-prod ABT*StepDone = ABT*StepDone
  
  action-type-construction :
    (t : BareType) -> 
    ∃[ As ] As , BareTHole ABT↦* t
  action-type-construction BareTHole = _ , ABT*StepDone
  action-type-construction BareTBase = _ , ABT*StepAct (ATBareDone ActInsertBase) ABT*StepDone
  action-type-construction (BareTVar x) = _ , ABT*StepAct (ATBareDone ActInsertTVar) ABT*StepDone
  action-type-construction (BareTArrow t1 t2) with action-type-construction t1 | action-type-construction t2
  ... | _ , steps1 | _ , steps2 = _ , ABT*StepActAppend steps1 (ABT*StepAct (ATBareDone ActWrapArrowOne) (act-in-arrow steps2))
  action-type-construction (BareTProd t1 t2) with action-type-construction t1 | action-type-construction t2
  ... | _ , steps1 | _ , steps2 = _ , ABT*StepActAppend steps1 (ABT*StepAct (ATBareDone ActWrapProdOne) (act-in-prod steps2))
  action-type-construction (BareTForall BHole t) with action-type-construction t
  ... | _ , steps = _ , ABT*StepActAppend steps (ABT*StepAct (ATBareDone ActWrapForall) ABT*StepDone)
  action-type-construction (BareTForall (BVar x) t) with action-type-construction t
  ... | _ , steps = _ , ABT*StepActAppend steps (ABT*StepActAppend (ABT*StepAct (ATBareDone ActWrapForall) ABT*StepDone) ((ABT*StepAct (ATBareDone ActInsertBinder) ABT*StepDone)))


  AB*StepActAppend : ∀{As1 As2 e e' e''} ->
    As1 , e AB↦* e' -> 
    As2 , e' AB↦* e'' ->
    (As1 ++ As2) , e AB↦* e'' 
  AB*StepActAppend (AB*StepAct x steps) step = AB*StepAct x (AB*StepActAppend steps step)
  AB*StepActAppend AB*StepDone step = step 

  act-in-ap : ∀{As2 e1 e2 e} ->
    As2 , e AB↦* e2 ->
    map nest-action As2 , BareEAp e1 e AB↦* BareEAp e1 e2
  act-in-ap (AB*StepAct x steps) = AB*StepAct (ABareApTwo x) (act-in-ap steps)
  act-in-ap AB*StepDone = AB*StepDone

  act-in-pair : ∀{As2 e1 e2 e} ->
    As2 , e AB↦* e2 ->
    map nest-action As2 , BareEPair e1 e AB↦* BareEPair e1 e2
  act-in-pair (AB*StepAct x steps) = AB*StepAct (ABarePairTwo x) (act-in-pair steps)
  act-in-pair AB*StepDone = AB*StepDone

  act-in-fun-ann : ∀{As x t t' e} ->
    As , t ABT↦* t' ->
    map nest-action-one As , BareEFun x t e AB↦* BareEFun x t' e
  act-in-fun-ann (ABT*StepAct x steps) = AB*StepAct (ABareFunOne x) (act-in-fun-ann steps)
  act-in-fun-ann ABT*StepDone = AB*StepDone

  act-in-asc : ∀{As t t' e} ->
    As , t ABT↦* t' ->
    map nest-action-one As , BareEAsc t e AB↦* BareEAsc t' e 
  act-in-asc (ABT*StepAct x steps) = AB*StepAct (ABareAscOne x) (act-in-asc steps)
  act-in-asc ABT*StepDone = AB*StepDone

  action-construction :
    (e : BareExp) -> 
    ∃[ As ] As , BareEHole AB↦* e
  action-construction BareEHole = _ , AB*StepDone
  action-construction BareEConst = _ , (AB*StepAct (ABareDone ActInsertConst) AB*StepDone)
  action-construction (BareEVar x) = _ , (AB*StepAct (ABareDone ActInsertVar) AB*StepDone)

  action-construction (BareEFun BHole t e) with action-construction e | action-type-construction t
  ... | _ , steps1 | _ , steps2 = _ , AB*StepActAppend steps1 (AB*StepAct (ABareDone ActWrapFun) (act-in-fun-ann steps2))
  action-construction (BareEFun (BVar x) t e) with action-construction e | action-type-construction t
  ... | _ , steps1 | _ , steps2 = _ , AB*StepActAppend steps1 (AB*StepActAppend (AB*StepAct (ABareDone ActWrapFun) (act-in-fun-ann steps2)) (AB*StepAct (ABareDone ActInsertBinder) AB*StepDone))
  action-construction (BareEAsc t e) with action-construction e | action-type-construction t
  ... | _ , steps1 | _ , steps2 = _ , AB*StepActAppend steps1 (AB*StepAct (ABareDone ActWrapAsc) (act-in-asc steps2))
  action-construction (BareEAp e1 e2) with action-construction e1 | action-construction e2
  ... | _ , steps1 | _ , steps2 = _ , AB*StepActAppend steps1 (AB*StepAct (ABareDone ActWrapApOne) (act-in-ap steps2))
  action-construction (BareEPair e1 e2) with action-construction e1 | action-construction e2
  ... | _ , steps1 | _ , steps2 = _ , AB*StepActAppend steps1 (AB*StepAct (ABareDone ActWrapPairOne) (act-in-pair steps2))
  action-construction (BareEProj s e) with action-construction e 
  ... | _ , steps = _ , AB*StepActAppend steps (AB*StepAct (ABareDone ActWrapProj) AB*StepDone)
  action-construction (BareETypFun x e) with action-construction e 
  ... | _ , steps = _ , AB*StepActAppend steps (AB*StepActAppend (AB*StepAct (ABareDone ActWrapTypFun) AB*StepDone) {! AB*StepAct (ABareDone ActInsertBinder) AB*StepDone  !})
  action-construction (BareETypAp e x) = {!   !}
   
  action-completeness :
    (e1 e2 : BareExp) -> 
    ∃[ As ] As , e1 AB↦* e2
  action-completeness e1 e2 with action-construction e2   
  ... | _ , steps = _ , AB*StepAct (ABareDone ActDelete) steps 