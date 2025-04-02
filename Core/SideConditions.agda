

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core

module Core.SideConditions where

  postulate
    _▸TArrow_,_,_ : Type -> Type -> Type -> Mark -> Set 

    _▸TProd_,_,_ : Type -> Type -> Type -> Mark -> Set 

    _,_▸TProj_,_ : Type -> ProdSide -> Type -> Mark -> Set 

    _▸TForall_,_,_ : Type -> Binding -> Type -> Mark -> Set 

    _~_,_ : Type -> Type -> Mark -> Set 

    ▸TArrow-unicity : ∀ {t t-in t-in' t-out t-out' m m'} ->
      t ▸TArrow t-in , t-out , m -> 
      t ▸TArrow t-in' , t-out' , m' -> 
      (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')

    ▸TProd-unicity : ∀ {t t-fst t-fst' t-snd t-snd' m m'} ->
      t ▸TProd t-fst , t-snd , m -> 
      t ▸TProd t-fst' , t-snd' , m' ->
      (t-fst ≡ t-fst' × t-snd ≡ t-snd' × m ≡ m')

    ▸TProj-unicity : ∀ {t s t-side t-side' m m'} ->
      t , s ▸TProj t-side , m -> 
      t , s ▸TProj t-side' , m' -> 
      (t-side ≡ t-side' × m ≡ m')

    ▸TForall-unicity : ∀ {t x x' t-body t-body' m m'} ->
      t ▸TForall x , t-body , m -> 
      t ▸TForall x' , t-body' , m' -> 
      (x ≡ x' × t-body ≡ t-body' × m ≡ m')

    ~-unicity : ∀ {syn ana m m'} ->
      syn ~ ana , m -> 
      syn ~ ana , m' ->
      m ≡ m'

    ▸TArrow-dec : 
      (t : Type) -> 
      ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸TArrow t-in , t-out , m

    ▸TProd-dec : 
      (t : Type) -> 
      ∃[ t-fst ] ∃[ t-snd ] ∃[ m ] t ▸TProd t-fst , t-snd , m

    ▸TProj-dec : 
      (s : ProdSide) -> 
      (t : Type) -> 
      ∃[ t' ] ∃[ m ] t , s ▸TProj t' , m

    ▸TForall-dec : 
      (t : Type) -> 
      ∃[ x ] ∃[ t-body ] ∃[ m ] t ▸TForall x , t-body , m

    ~-dec : 
      (syn ana : Type) -> 
      ∃[ m ] syn ~ ana , m 
  
  -- data _▸TArrow_,_,_ : Type -> Type -> Type -> Mark -> Set where 
  --   MArrowBase :
  --     TBase ▸TArrow THole , THole , ✖
  --   MArrowHole :
  --     THole ▸TArrow THole , THole , ✔
  --   MArrowArrow : ∀ {t1 t2} -> 
  --     (TArrow t1 t2) ▸TArrow t1 , t2 , ✔
  --   MArrowProd : ∀ {t1 t2} -> 
  --     (TProd t1 t2) ▸TArrow THole , THole , ✖
  --   MArrowVar : ∀ {x} ->
  --     (TVar x) ▸TArrow THole , THole , ✖
  --   MArrowForall : ∀ {x t} ->
  --     (TForall x t) ▸TArrow THole , THole , ✖
  
  -- data _▸TProd_,_,_ : Type -> Type -> Type -> Mark -> Set where 
  --   MProdBase :
  --     TBase ▸TProd THole , THole , ✖
  --   MProdHole :
  --     THole ▸TProd THole , THole , ✔
  --   MProdArrow : ∀ {t1 t2} -> 
  --     (TArrow t1 t2) ▸TProd THole , THole , ✖
  --   MProdProd : ∀ {t1 t2} -> 
  --     (TProd t1 t2) ▸TProd t1 , t2 , ✔
  --   MProdVar : ∀ {x} ->
  --     (TVar x) ▸TProd THole , THole , ✖
  --   MProdForall : ∀ {x t} ->
  --     (TForall x t) ▸TProd THole , THole , ✖

  -- data _,_▸TProj_,_ : Type -> ProdSide -> Type -> Mark -> Set where 
  --   MProdFst : ∀ {t t-fst t-snd m} -> 
  --     t ▸TProd t-fst , t-snd , m ->
  --     t , Fst ▸TProj t-fst , m 
  --   MProdSnd : ∀ {t t-fst t-snd m} ->
  --     t ▸TProd t-fst , t-snd , m ->
  --     t , Snd ▸TProj t-snd , m

  -- data _▸TForall_,_,_ : Type -> Binding -> Type -> Mark -> Set where 
  --   MForallBase :
  --     TBase ▸TForall BHole , THole , ✖
  --   MForallHole :
  --     THole ▸TForall BHole , THole , ✔
  --   MForallArrow : ∀ {t1 t2} -> 
  --     (TArrow t1 t2) ▸TForall BHole , THole , ✖
  --   MForallProd : ∀ {t1 t2} -> 
  --     (TProd t1 t2) ▸TForall BHole , THole , ✖
  --   MForallVar : ∀ {x} ->
  --     (TVar x) ▸TForall BHole , THole , ✖
  --   MForallForall : ∀ {x t} ->
  --     (TForall x t) ▸TForall x , t , ✖

    -- ConsistHoleL : ∀ {t} -> THole ~ t , ✔
    -- ConsistHoleR : ∀ {t} -> t ~ THole , ✔
    -- ConsistBase : TBase ~ TBase , ✔
    -- ConsistArr : ∀ {t1 t2 t3 t4 m1 m2} -> 
    --   t1 ~ t3 , m1 -> 
    --   t2 ~ t4 , m2 -> 
    --   ((TArrow t1 t2) ~ (TArrow t3 t4) , (m1 ⊓M m2))
    -- ConsistProd : ∀ {t1 t2 t3 t4 m1 m2} -> 
    --   t1 ~ t3 , m1 -> 
    --   t2 ~ t4 , m2 -> 
    --   ((TProd t1 t2) ~ (TProd t3 t4) , (m1 ⊓M m2))
    -- InconsistBaseArr : ∀ {t1 t2} ->
    --   TBase ~ (TArrow t1 t2) , ✖
    -- InconsistArrBase : ∀ {t1 t2} ->
    --   (TArrow t1 t2) ~ TBase , ✖
    -- InconsistBaseProd : ∀ {t1 t2} ->
    --   TBase ~ (TProd t1 t2) , ✖
    -- InconsistProdBase : ∀ {t1 t2} ->
    --   (TProd t1 t2) ~ TBase , ✖
    -- InconsistArrProd : ∀ {t1 t2 t3 t4} ->
    --   (TArrow t1 t2) ~ (TProd t3 t4) , ✖
    -- InconsistProdArr : ∀ {t1 t2 t3 t4} ->
    --   (TProd t1 t2) ~ (TArrow t3 t4) , ✖
