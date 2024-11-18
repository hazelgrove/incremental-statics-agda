open import Data.Nat hiding (_+_)
open import Data.Unit 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core

module Core.Merge where

-- MergeInfo (t1 , n1) (t2 , n2) (t3 , n3) holds with:
-- (t1 , n1) is the stored info
-- (t2 , n2) is the calculated true info 
-- (t3 , n3) is the info that should be passed along
-- and ensures that the stored info is compatible with the real info.
-- This is the case when t1 and t2 are the same at the points where n2 is old. 
-- Where n2 is all new, the "real" info hasn't been propagated yet and doesn't 
-- need to have been stored already. It doesn't matter whether n1 is new or old. 

data TSingleton : Type -> Set where 
  TBaseSingleton : TSingleton TBase
  THoleSingleton : TSingleton THole

data NSingleton : Newness -> Set where 
  NNewSingleton : NSingleton New
  NOldSingleton : NSingleton Old

-- data NTWf : NewType -> Set where 
--   NTWfSingleton : ∀ {t n} ->
--     TSingleton t -> 
--     NSingleton n ->
--     NTWf (t , n)
--   NTWfArrow : ∀ {t1 t2 n n1 n2} ->
--     (n ▸NArrow n1 , n2) ->
--     NTWf (t1 , n1) ->
--     NTWf (t2 , n2) ->
--     NTWf (TArrow t1 t2 , n)

data NTWf : NewType -> Set where 
  NTWfSingleton : ∀ {t n} ->
    NSingleton n ->
    NTWf (t , n)
  NTWfArrow : ∀ {t1 t2 n1 n2} ->
    NTWf (t1 , n1) ->
    NTWf (t2 , n2) ->
    NTWf (TArrow t1 t2 , NArrow n1 n2)

-- structural
data NTSWf : NewType -> Set where 
  NTSWfSingleton : ∀ {t n} ->
    TSingleton t -> 
    NSingleton n ->
    NTSWf (t , n)
  NTSWfArrow : ∀ {t1 t2 n1 n2} ->
    NTSWf (t1 , n1) ->
    NTSWf (t2 , n2) ->
    NTSWf (TArrow t1 t2 , NArrow n1 n2)

data NCompact : Newness -> Set where
  NCOld : NCompact Old 
  NCNew : NCompact New
  NCArrow : ∀ {n1 n2} ->
      NCompact n1 -> 
      NCompact n2 ->
      (¬(n1 ≡ New × n2 ≡ New)) ->
      (¬(n1 ≡ Old × n2 ≡ Old)) ->
      NCompact (NArrow n1 n2) 

-- compact
data NTCWf : NewType -> Set where 
  NTCWfSingleton : ∀ {t n} ->
    NSingleton n ->
    NTCWf (t , n)
  NTCWfArrow : ∀ {t1 t2 n1 n2} ->
    NCompact (NArrow n1 n2) ->
    NTCWf (t1 , n1) ->
    NTCWf (t2 , n2) ->
    NTCWf (TArrow t1 t2 , NArrow n1 n2)

structify : NewType -> NewType 
structify (TBase , n) = (TBase , n)
structify (THole , n) = (THole , n)
structify (TArrow t1 t2 , Old) with structify (t1 , Old) | structify (t2 , Old)
... | (t1' , n1) | (t2' , n2) = TArrow t1' t2' , NArrow n1 n2
structify (TArrow t1 t2 , New) with structify (t1 , New) | structify (t2 , New)
... | (t1' , n1) | (t2' , n2) = TArrow t1' t2' , NArrow n1 n2
structify (TArrow t1 t2 , NArrow n1 n2) with structify (t1 , n1) | structify (t2 , n2)
... | (t1' , n1') | (t2' , n2') = TArrow t1' t2' , NArrow n1' n2'

-- structify-wf : {t : NewType} -> (NTWf t) -> (NTSWf (structify t))
-- structify-wf {TBase , n} (NTWfSingleton s1 s2) = NTSWfSingleton s1 s2
-- structify-wf {THole , n} (NTWfSingleton s1 s2) = NTSWfSingleton s1 s2
-- structify-wf {TArrow t1 t2 , Old} (NTWfArrow MNArrowOld wf1 wf2) with structify-wf {t1 , Old} wf1 | structify-wf {t2 , Old} wf2
-- ... | wf1' | wf2' = NTSWfArrow wf1' wf2'
-- structify-wf {TArrow t1 t2 , New} (NTWfArrow MNArrowNew wf1 wf2) with structify-wf {t1 , New} wf1 | structify-wf {t2 , New} wf2
-- ... | wf1' | wf2' = NTSWfArrow wf1' wf2'
-- structify-wf {TArrow t1 t2 , NArrow n1 n2} (NTWfArrow MNArrowArrow wf1 wf2) with structify-wf {t1 , n1} wf1 | structify-wf {t2 , n2} wf2
-- ... | wf1' | wf2' = NTSWfArrow wf1' wf2'

structify-wf : {t : NewType} -> (NTCWf t) -> (NTSWf (structify t))
structify-wf {TBase , n} (NTCWfSingleton x) = NTSWfSingleton TBaseSingleton x
structify-wf {THole , n} (NTCWfSingleton x) = NTSWfSingleton THoleSingleton x
structify-wf {TArrow t1 t2 , Old} (NTCWfSingleton NOldSingleton) with structify-wf {t1 , Old} (NTCWfSingleton NOldSingleton) | structify-wf {t2 , Old} (NTCWfSingleton NOldSingleton)
... | wf1' | wf2' = NTSWfArrow wf1' wf2'
structify-wf {TArrow t1 t2 , New} (NTCWfSingleton NNewSingleton) with structify-wf {t1 , New} (NTCWfSingleton NNewSingleton) | structify-wf {t2 , New} (NTCWfSingleton NNewSingleton)
... | wf1' | wf2' = NTSWfArrow wf1' wf2'
structify-wf {TArrow t1 t2 , (NArrow n1 n2)} (NTCWfArrow _ wf1 wf2) with structify-wf {t1 , n1} wf1 | structify-wf {t2 , n2} wf2
... | wf1' | wf2' = NTSWfArrow wf1' wf2'

compactify-newness : Newness -> Newness
compactify-newness Old = Old 
compactify-newness New = New 
compactify-newness (NArrow n1 n2) with compactify-newness n1 | compactify-newness n2 
... | Old | Old = Old
... | New | New = New
... | n1' | n2' = NArrow n1' n2'

compactify : NewType -> NewType 
compactify (t , n) = (t , compactify-newness n)

compactify-newness-compact : (n : Newness) -> (NCompact (compactify-newness n))
compactify-newness-compact Old = NCOld
compactify-newness-compact New = NCNew
compactify-newness-compact (NArrow n1 n2) with compactify-newness n1 | compactify-newness n2 | compactify-newness-compact n1 | compactify-newness-compact n2 
... | Old | Old | _ | _ = NCOld
... | New | New | _ | _ = NCNew
... | Old | New | c1 | c2 = NCArrow c1 c2 (λ ()) (λ ())
... | Old | NArrow n2' n2'' | c1 | c2 = NCArrow c1 c2 (λ ()) (λ ())
... | New | Old | c1 | c2 =  NCArrow c1 c2 (λ ()) (λ ())
... | New | NArrow n2' n2'' | c1 | c2 =  NCArrow c1 c2 (λ ()) (λ ())
... | NArrow n1' n1'' | Old | c1 | c2 =  NCArrow c1 c2 (λ ()) (λ ())
... | NArrow n1' n1'' | New | c1 | c2 =  NCArrow c1 c2 (λ ()) (λ ())
... | NArrow n1' n1'' | NArrow n2' n2'' | c1 | c2 =  NCArrow c1 c2 (λ ()) (λ ())

compact-struct-wf-lemma : ∀ {t n} ->
  NTSWf (t , n) ->
  NTCWf (t , compactify-newness n)
compact-struct-wf-lemma {n = n} (NTSWfSingleton x NNewSingleton) = NTCWfSingleton NNewSingleton
compact-struct-wf-lemma {n = n} (NTSWfSingleton x NOldSingleton) = NTCWfSingleton NOldSingleton
compact-struct-wf-lemma {n = NArrow n1 n2} (NTSWfArrow wf1 wf2) with compactify-newness n1 | compactify-newness n2 | compact-struct-wf-lemma wf1 | compact-struct-wf-lemma wf2 
... | Old | Old | c1 | c2 = NTCWfSingleton NOldSingleton
... | New | New | c1 | c2 = NTCWfSingleton NNewSingleton
... | Old | New | c1 | c2 = NTCWfArrow (NCArrow NCOld NCNew (λ ()) (λ ())) c1 c2
... | New | Old | c1 | c2 = NTCWfArrow (NCArrow NCNew NCOld (λ ()) (λ ())) c1 c2
... | Old | NArrow n2' n2'' | wf1 | (NTCWfArrow c2 wf2 wf3) = NTCWfArrow (NCArrow NCOld c2 (λ ()) (λ ())) wf1 (NTCWfArrow c2 wf2 wf3)
... | New | NArrow n2' n2'' | wf1 | (NTCWfArrow c2 wf2 wf3) = NTCWfArrow (NCArrow NCNew c2 (λ ()) (λ ())) wf1 (NTCWfArrow c2 wf2 wf3)
... | NArrow n1' n1'' | Old | (NTCWfArrow c1 wf1 wf2) | wf3 = NTCWfArrow (NCArrow c1 NCOld (λ ()) (λ ())) (NTCWfArrow c1 wf1 wf2) wf3
... | NArrow n1' n1'' | New | (NTCWfArrow c1 wf1 wf2) | wf3 = NTCWfArrow (NCArrow c1 NCNew (λ ()) (λ ())) (NTCWfArrow c1 wf1 wf2) wf3
... | NArrow n1' n1'' | NArrow n2' n2'' | (NTCWfArrow c1 wf1 wf2) | (NTCWfArrow c2 wf3 wf4) = NTCWfArrow (NCArrow c1 c2 ((λ ())) ((λ ()))) (NTCWfArrow c1 wf1 wf2) (NTCWfArrow c2 wf3 wf4)

compatify-components : ∀ {n1 n2 n3 n4} ->
    (compactify-newness (NArrow n1 n2) ≡ (NArrow n3 n4)) ->
    (compactify-newness n1 ≡ n3 × compactify-newness n2 ≡ n4)
compatify-components {n1} {n2} eq with compactify-newness n1 | compactify-newness n2 | eq
... | Old | New | refl = refl , refl
... | Old | NArrow n2' n2'' | refl = refl , refl
... | New | Old | refl = refl , refl
... | New | NArrow n2' n2'' | refl = refl , refl
... | NArrow n1' n1'' | Old | refl = refl , refl
... | NArrow n1' n1'' | New | refl = refl , refl
... | NArrow n1' n1'' | NArrow n2' n2'' | refl = refl , refl

compactify-wf : {t : NewType} -> (NTSWf t) -> (NTCWf (compactify t))
compactify-wf {t , Old} wf = NTCWfSingleton NOldSingleton
compactify-wf {t , New} wf = NTCWfSingleton NNewSingleton
compactify-wf {TArrow t1 t2 , NArrow n1 n2} (NTSWfArrow wf1 wf2) with compactify-newness (NArrow n1 n2) in eq | compactify-newness-compact (NArrow n1 n2)
... | Old | c = NTCWfSingleton NOldSingleton
... | New | c = NTCWfSingleton NNewSingleton
... | NArrow n' n'' | NCArrow c1 c2 neq1 neq2 with (compatify-components {n1} {n2} eq) 
... | refl , refl = NTCWfArrow (NCArrow c1 c2 neq1 neq2) (compact-struct-wf-lemma wf1) (compact-struct-wf-lemma wf2)

-- precondition: newtype structures match (only New or Old at type leaves)
data _S▷_==_ : NewType -> NewType -> NewType -> Set where 
  SMergeInfoNew : ∀ {t1 t2 n2} -> 
    (t1 , New) S▷ (t2 , n2) == (t1 , New)
  SMergeInfoOld : ∀ {t1 n2} -> 
    (t1 , Old) S▷ (t1 , n2) == (t1 , n2)
  SMergeInfoArrow : ∀ {t1 t2 t3 t4 t5 t6 n1 n2 n3 n4 n5 n6} -> 
    (t1 , n1) S▷ (t3 , n3) == (t5 , n5) ->
    (t2 , n2) S▷ (t4 , n4) == (t6 , n6) ->
    (TArrow t1 t2 , NArrow n1 n2) S▷ (TArrow t3 t4 , NArrow n3 n4) == (TArrow t5 t6 , NArrow n5 n6)


smerge-lassoc : ∀ {t1 t2 t3 t23 t123} ->
  NTSWf t1 ->
  NTSWf t2 ->
  NTSWf t3 ->
  t2 S▷ t3 == t23 ->
  t1 S▷ t23 == t123 ->
  ∃[ t12 ] (t1 S▷ t2 == t12 × t12 S▷ t3 == t123)
smerge-lassoc wf1 wf2 wf3 _ SMergeInfoNew = (_ , New) , SMergeInfoNew , SMergeInfoNew
smerge-lassoc wf1 wf2 wf3 SMergeInfoNew SMergeInfoOld = (_ , New) , SMergeInfoOld , SMergeInfoNew
smerge-lassoc wf1 wf2 wf3 SMergeInfoOld SMergeInfoOld = (_ , Old) , SMergeInfoOld , SMergeInfoOld
smerge-lassoc wf1 (NTSWfSingleton () _) wf3 SMergeInfoOld (SMergeInfoArrow m2 m3)
smerge-lassoc (NTSWfSingleton () _) wf2 wf3 (SMergeInfoArrow m1 m2) SMergeInfoOld
smerge-lassoc (NTSWfArrow wf1 wf2) (NTSWfArrow wf3 wf4) (NTSWfArrow wf5 wf6) (SMergeInfoArrow m1 m2) (SMergeInfoArrow m3 m4) 
  with smerge-lassoc wf1 wf3 wf5 m1 m3 | smerge-lassoc wf2 wf4 wf6 m2 m4 
... | t13 , m5 , m6 | t24 , m7 , m8 = _ , SMergeInfoArrow m5 m7 , SMergeInfoArrow m6 m8


data _▷_==_ : NewType -> NewType -> NewType -> Set where 
  MergeInfoNew : ∀ {t1 t2 n2} -> 
    (t1 , New) ▷ (t2 , n2) == (t1 , New)
  MergeInfoOld : ∀ {t1 n2} -> 
    (t1 , Old) ▷ (t1 , n2) == (t1 , n2)
  MergeInfoArrow : ∀ {t1 t2 t3 t4 t5 t6 n n1 n2 n3 n4 n5 n6 n7} -> 
    n ▸NArrow n3 , n4 ->
    (t1 , n1) ▷ (t3 , n3) == (t5 , n5) ->
    (t2 , n2) ▷ (t4 , n4) == (t6 , n6) ->
    narrow n5 n6 ≡ n7 ->
    (TArrow t1 t2 , NArrow n1 n2) ▷ (TArrow t3 t4 , n) == (TArrow t5 t6 , n7)

-- data MergeInfo : NewType -> NewType -> NewType -> Set where 
--   MergeInfoNew : ∀ {t1 t2 n1} -> 
--     MergeInfo (t1 , n1) (t2 , New) (t2 , New)    
--   MergeInfoOld : ∀ {t1 n1} ->    
--     MergeInfo (t1 , n1) (t1 , Old) (t1 , n1)   
--   MergeInfoArrow : ∀ {t1 t2 t3 t4 t5 t6 n n1 n2 n3 n4 n5 n6 n7} -> 
--     n ▸NArrow n1 , n2 -> 
--     MergeInfo (t1 , n1) (t3 , n3) (t5 , n5) ->  
--     MergeInfo (t2 , n2) (t4 , n4) (t6 , n6) ->           
--     narrow n5 n6 ≡ n7 ->   
--     MergeInfo (TArrow t1 t2 , n) (TArrow t3 t4 , NArrow n3 n4) (TArrow t5 t6 , n7) 