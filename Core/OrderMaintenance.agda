open import Prelude
open import Relation.Binary.PropositionalEquality hiding (inspect)

module Core.OrderMaintenance where

mutual 
  data OM : Set where
    OMInit : OM
    OMInsert : 
      {om : OM} ->
      (on : ON om) ->
      OM
    
  data ON : OM -> Set where 
    ONInit : ON OMInit
    ONInsertOld : 
      {om : OM} ->
      (on : ON om) ->
      (on-old : ON om) ->
      ON (OMInsert on)
    ONInsertNew : 
      {om : OM} ->
      (on : ON om) ->
      ON (OMInsert on)

data CompareResult : Set where 
  LT : CompareResult
  EQ : CompareResult 
  GT : CompareResult

compare : {om : OM} -> (ON om) -> (ON om) -> CompareResult
compare {OMInit} ONInit ONInit = EQ
compare {OMInsert on} (ONInsertOld .on on1) (ONInsertOld .on on2) = compare on1 on2
compare {OMInsert on} (ONInsertOld .on on-old) (ONInsertNew .on) with compare on on-old
compare {OMInsert on} (ONInsertOld .on on-old) (ONInsertNew .on) | LT = LT
compare {OMInsert on} (ONInsertOld .on on-old) (ONInsertNew .on) | EQ = LT
compare {OMInsert on} (ONInsertOld .on on-old) (ONInsertNew .on) | GT = GT
compare {OMInsert on} (ONInsertNew .on) (ONInsertOld .on on-old) with compare on on-old
compare {OMInsert on} (ONInsertNew .on) (ONInsertOld .on on-old) | LT = LT
compare {OMInsert on} (ONInsertNew .on) (ONInsertOld .on on-old) | EQ = GT
compare {OMInsert on} (ONInsertNew .on) (ONInsertOld .on on-old) | GT = GT
compare {OMInsert on} (ONInsertNew .on) (ONInsertNew .on) = EQ


-- data _<OM_ : {om : OM} -> (ON om) -> (ON om) -> Set where 
--   <OMInsertOld : {om : OM} -> {on on-old : ON om} -> 
--     (on-old <OM on) ->
--     (ONInsertOld on on-old) <OM (ONInsertNew on)
--   <OMInsertNew : {om : OM} -> {on : ON om} -> 
--     (ONInsertOld on on) <OM (ONInsertNew on)


ONE : OM 
ONE = OMInit

ONE-zero : ON ONE 
ONE-zero = ONInit

TWO : OM 
TWO = OMInsert ONE-zero

TWO-zero : ON TWO 
TWO-zero = ONInsertOld ONE-zero ONE-zero

TWO-one : ON TWO 
TWO-one = ONInsertNew ONE-zero

equation : (compare TWO-zero TWO-one) ≡ LT
equation = refl
 
  
-- data _∈OM_ : ON -> OM -> Set where 
--   EOMInit : ONInit ∈OM OMInit