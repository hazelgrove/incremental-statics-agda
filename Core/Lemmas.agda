
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) 
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Prelude
open import Core.Core
open import Core.SideConditions
open import Core.Environment
open import Core.WellFormed
open import Core.MarkingUnicity

module Core.Lemmas where

  data =▷ {A : Set} : ○ A -> ○ A -> Set where 
    =▷★ : ∀ {s t} -> 
      =▷ s (t , ★)
    =▷Refl : ∀ {s} -> 
      =▷ s s

  data ◁▷ {A : Set} : ○ A -> ○ A -> Set where 
    ◁▷C : ∀ {t n n'} -> 
      ◁▷ (t , n) (t , n')

  max-dirty : (n : Dirtiness) -> n ⊓ ★ ≡ ★ 
  max-dirty • = refl
  max-dirty ★ = refl

  ~DVoid-right : ∀ {t m} ->
    t ~D □ , m ->
    m ≡ ✔
  ~DVoid-right ~DVoidL = refl
  ~DVoid-right ~DVoidR = refl

  ~D-unless : ∀ {t1 t2} ->
    DUnless t1 t2 ~D t2 , ✔
  ~D-unless {t2 = □} = ~DVoidR
  ~D-unless {t2 = ■ x} = ~DVoidL 

  dirty-through-~N-left : ∀ {d t m} ->
    d ~N (t , ★) , m -> 
    ∃[ m' ] m ≡ (m' , ★)
  dirty-through-~N-left (~N-pair {n1 = n1} consist) rewrite max-dirty n1 = _ , refl

  ▶Same : ∀ {n} ->
    {A : Set} ->
    {a : A} ->
    ▶ (a , n) a
  ▶Same {•} = ▶•
  ▶Same {★} = ▶★

  ▶★-max-r : ∀ {n} -> 
    {A : Set} -> 
    {a a' : A} ->
    ▶ (a , (n ⊓ ★)) a'
  ▶★-max-r {n = n} rewrite max-dirty n = ▶★

  =▷★-max-r : ∀ {n n'} -> 
    {A : Set} -> 
    {a a' : A} ->
    =▷ (a , n') (a' , (n ⊓ ★))
  =▷★-max-r {n = n} rewrite max-dirty n = =▷★

  -- not true lol
  -- ▷-trans : ∀ {a b c} ->
  --   ▷ a b -> 
  --   ▷ b c -> 
  --   ▷ a c 
  -- ▷-trans (▷Pair ▶★) (▷Pair ▶★) = ▷Pair ▶★
  -- ▷-trans (▷Pair ▶★) (▷Pair ▶•) = ▷Pair ▶★
  -- ▷-trans (▷Pair ▶•) (▷Pair ▶★) = {!   !}
  -- ▷-trans (▷Pair ▶•) (▷Pair ▶•) = {!   !}

  -- ▸TArrow-dec : 
  --   (t : Type) -> 
  --   ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸TArrow t-in , t-out , m
  -- ▸TArrow-dec TBase = THole , THole , ✖ , MArrowBase
  -- ▸TArrow-dec THole = THole , THole , ✔ , MArrowHole
  -- ▸TArrow-dec (TArrow t1 t2) = t1 , t2 , ✔ , MArrowArrow
  -- ▸TArrow-dec (TProd t1 t2) = THole , THole , ✖ , MArrowProd

  ▸DTArrow-dec : 
    (t : Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸DTArrow t-in , t-out , m
  ▸DTArrow-dec □ = □ , □ , ✔ , DTArrowNone
  ▸DTArrow-dec (■ t) with ▸TArrow-dec t 
  ... | t1 , t2 , m , match = ■ t1 , ■ t2 , m , DTArrowSome match

  ▸NTArrow-dec : 
    (d : ○Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] d ▸NTArrow t-in , t-out , m
  ▸NTArrow-dec (d , n) with ▸DTArrow-dec d 
  ... | t1 , t2 , m , match = (t1 , n) , (t2 , n) , (m , n) , NTArrowC match

  -- ▸TProd-dec : 
  --   (t : Type) -> 
  --   ∃[ t-fst ] ∃[ t-snd ] ∃[ m ] t ▸TProd t-fst , t-snd , m
  -- ▸TProd-dec TBase = THole , THole , ✖ , MProdBase
  -- ▸TProd-dec THole = THole , THole , ✔ , MProdHole
  -- ▸TProd-dec (TArrow t t₁) = THole , THole , ✖ , MProdArrow
  -- ▸TProd-dec (TProd t t₁) = t , t₁ , ✔ , MProdProd

  ▸DTProd-dec : 
    (t : Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸DTProd t-in , t-out , m
  ▸DTProd-dec □ = □ , □ , ✔ , DTProdNone
  ▸DTProd-dec (■ t) with ▸TProd-dec t 
  ... | t1 , t2 , m , match = ■ t1 , ■ t2 , m , DTProdSome match

  ▸NTProd-dec : 
    (d : ○Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] d ▸NTProd t-in , t-out , m
  ▸NTProd-dec (d , n) with ▸DTProd-dec d 
  ... | t1 , t2 , m , match = (t1 , n) , (t2 , n) , (m , n) , NTProdC match

  ▸DTProj-dec : 
    (s : ProdSide) -> 
    (t : Data) -> 
    ∃[ t' ] ∃[ m ] t , s ▸DTProj t' , m
  ▸DTProj-dec s □ = □ , ✔ , DTProjNone
  ▸DTProj-dec s (■ t) with ▸TProj-dec s t 
  ... | t' , m , match = ■ t' , m , DTProjSome match

  ▸NTProj-dec : 
    (s : ProdSide) -> 
    (d : ○Data) -> 
    ∃[ t ] ∃[ m ] d , s ▸NTProj t , m
  ▸NTProj-dec s (d , n) with ▸DTProj-dec s d 
  ... | t , m , match = (t , n) , (m , n) , NTProjC match

  ▸DTForall-dec : 
    (d : Data) -> 
    ∃[ x ] ∃[ t ] ∃[ m ] d ▸DTForall x , t , m
  ▸DTForall-dec □ = BHole , □ , ✔ , DTForallNone
  ▸DTForall-dec (■ t) with ▸TForall-dec t
  ... | x , t' , m , match = x , ■ t' , m , DTForallSome match

  ▸NTForall-dec : 
    (d : ○Data) -> 
    ∃[ x ] ∃[ t ] ∃[ m ] d ▸NTForall x , t , m
  ▸NTForall-dec (d , n) with ▸DTForall-dec d
  ... | x , t' , m , match = x , (t' , n) , (m , n) , NTForallC match

  ▸DTForallBind-dec : 
    (d : Data) -> 
    (x : Binding) ->
    ∃[ t ] ∃[ m ] d , x ▸DTForallBind t , m
  ▸DTForallBind-dec □ x = □ , ✔ , DTForallBindNone
  ▸DTForallBind-dec (■ t) x with ▸TForallBind-dec t x
  ... | t' , m , match = ■ t' , m , DTForallBindSome match

  -- ~-dec : 
  --   (syn ana : Type) -> 
  --   ∃[ m ] syn ~ ana , m 
  -- ~-dec THole _ = ✔ , ConsistHoleL
  -- ~-dec _ THole = ✔ , ConsistHoleR
  -- ~-dec TBase TBase = ✔ , ConsistBase
  -- ~-dec TBase (TArrow _ _) = ✖ , InconsistBaseArr
  -- ~-dec TBase (TProd _ _) = ✖ , InconsistBaseProd
  -- ~-dec (TArrow _ _) TBase = ✖ , InconsistArrBase
  -- ~-dec (TArrow syn1 syn2) (TArrow ana1 ana2) with ~-dec syn1 ana1 | ~-dec syn2 ana2 
  -- ... | m1 , consist1 | m2 , consist2 = (m1 ⊓M m2) , ConsistArr consist1 consist2
  -- ~-dec (TArrow _ _) (TProd _ _ ) = ✖ , InconsistArrProd 
  -- ~-dec (TProd t1 t2) TBase = ✖ , InconsistProdBase
  -- ~-dec (TProd t1 t2) (TArrow t3 t4) = ✖ , InconsistProdArr
  -- ~-dec (TProd t1 t2) (TProd t3 t4) with ~-dec t1 t3 | ~-dec t2 t4 
  -- ... | m1 , consist1 | m2 , consist2 = (m1 ⊓M m2) , ConsistProd consist1 consist2

  ~D-dec : 
    (syn ana : Data) -> 
    ∃[ m ] syn ~D ana , m 
  ~D-dec □ _ = ✔ , ~DVoidL
  ~D-dec (■ syn) □ = ✔ , ~DVoidR
  ~D-dec (■ syn) (■ ana) with ~-dec syn ana 
  ... | m , consist = m , (~DSome consist)

  ~N-dec : 
    (syn ana : ○Data) -> 
    ∃[ m ] syn ~N ana , m 
  ~N-dec (syn-d , syn-n) (ana-d , ana-n) with ~D-dec syn-d ana-d
  ... | m , consist = (m , (syn-n ⊓ ana-n)) , ~N-pair consist

  DSub-dec : 
    (t : Type) -> 
    (x : Binding) ->
    (d1 : Data) ->
    ∃[ d2 ] DSub t x d1 d2 
  DSub-dec t x □ = □ , NSubVoid
  DSub-dec t x (■ t1) with Sub-dec t x t1 
  ... | t2 , sub = ■ t2 , NSubSome sub

  NSub-dec : 
    (t : ○Type) -> 
    (x : Binding) ->
    (d1 : ○Data) ->
    ∃[ d2 ] NSub t x d1 d2 
  NSub-dec (t , n1) x (d , n2) with DSub-dec t x d
  ... | d' , sub = (d' , (n1 ⊓ n2)) , NSub-pair sub
  
  ▸DTArrow-unicity : ∀ {d t-in t-in' t-out t-out' m m'} ->
    d ▸DTArrow t-in , t-out , m -> 
    d ▸DTArrow t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸DTArrow-unicity DTArrowNone DTArrowNone = refl , refl , refl
  ▸DTArrow-unicity (DTArrowSome match1) (DTArrowSome match2) with ▸TArrow-unicity match1 match2
  ... | refl , refl , refl = refl , refl , refl
  
  ▸NTArrow-unicity : ∀ {d t-in t-in' t-out t-out' m m'} ->
    d ▸NTArrow t-in , t-out , m -> 
    d ▸NTArrow t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸NTArrow-unicity (NTArrowC match1) (NTArrowC match2) with ▸DTArrow-unicity match1 match2 
  ... | refl , refl , refl = refl , refl , refl

  ▸DTProd-unicity : ∀ {d t-in t-in' t-out t-out' m m'} ->
    d ▸DTProd t-in , t-out , m -> 
    d ▸DTProd t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸DTProd-unicity DTProdNone DTProdNone = refl , refl , refl
  ▸DTProd-unicity (DTProdSome match1) (DTProdSome match2) with ▸TProd-unicity match1 match2
  ... | refl , refl , refl = refl , refl , refl
  
  ▸DTProj-unicity : ∀ {d s t t' m m'} ->
    d , s ▸DTProj t , m -> 
    d , s ▸DTProj t' , m' -> 
    (t ≡ t' × m ≡ m')
  ▸DTProj-unicity DTProjNone DTProjNone = refl , refl
  ▸DTProj-unicity (DTProjSome match1) (DTProjSome match2) with ▸TProj-unicity match1 match2
  ... | refl , refl = refl , refl

  ▸NTProj-unicity : ∀ {d s t t' m m'} ->
    d , s ▸NTProj t , m -> 
    d , s ▸NTProj t' , m' -> 
    (t ≡ t' × m ≡ m')
  ▸NTProj-unicity (NTProjC match1) (NTProjC match2) with ▸DTProj-unicity match1 match2 
  ... | refl , refl = refl , refl
  
  ▸DTForall-unicity : ∀ {d x x' t-body t-body' m m'} ->
    d ▸DTForall x , t-body , m -> 
    d ▸DTForall x' , t-body' , m' -> 
    (x ≡ x' × t-body ≡ t-body' × m ≡ m')
  ▸DTForall-unicity DTForallNone DTForallNone = refl , refl , refl
  ▸DTForall-unicity (DTForallSome match1) (DTForallSome match2) with ▸TForall-unicity match1 match2
  ... | refl , refl , refl = refl , refl , refl
  
  ▸NTForall-unicity : ∀ {d x x' t-body t-body' m m'} ->
    d ▸NTForall x , t-body , m -> 
    d ▸NTForall x' , t-body' , m' -> 
    (x ≡ x' × t-body ≡ t-body' × m ≡ m')
  ▸NTForall-unicity (NTForallC match1) (NTForallC match2) with ▸DTForall-unicity match1 match2 
  ... | refl , refl , refl = refl , refl , refl

  ▸DTForallBind-unicity : ∀ {d x t-body t-body' m m'} ->
    d , x ▸DTForallBind t-body , m -> 
    d , x ▸DTForallBind t-body' , m' -> 
    (t-body ≡ t-body' × m ≡ m')
  ▸DTForallBind-unicity DTForallBindNone DTForallBindNone = refl , refl
  ▸DTForallBind-unicity (DTForallBindSome match1) (DTForallBindSome match2) with ▸TForallBind-unicity match1 match2
  ... | refl , refl = refl , refl
  
  DSub-unicity : ∀ {t x d1 d2 d2'} -> 
    DSub t x d1 d2  -> 
    DSub t x d1 d2'  -> 
    d2 ≡ d2'
  DSub-unicity NSubVoid NSubVoid = refl
  DSub-unicity (NSubSome x) (NSubSome x₁) rewrite sub-unicity x x₁ = refl

  ~D-unicity : ∀ {syn ana m m'} ->
    syn ~D ana , m -> 
    syn ~D ana , m' ->
    m ≡ m'
  ~D-unicity ~DVoidL ~DVoidL = refl
  ~D-unicity ~DVoidL ~DVoidR = refl
  ~D-unicity ~DVoidR ~DVoidL = refl
  ~D-unicity ~DVoidR ~DVoidR = refl
  ~D-unicity (~DSome consist1) (~DSome consist2) = ~-unicity consist1 consist2

  ~N-unicity : ∀ {syn ana m m'} ->
    syn ~N ana , m -> 
    syn ~N ana , m' ->
    m ≡ m'
  ~N-unicity (~N-pair consist1) (~N-pair consist2) rewrite ~D-unicity consist1 consist2 = refl

  -- not used
  -- ∈N-unicity : ∀ {x t t' Γ m m'} ->
  --   x , t ∈N Γ , m ->
  --   x , t' ∈N Γ , m' ->
  --   (t ≡ t' × m ≡ m')
  -- ∈N-unicity InCtxEmpty InCtxEmpty = refl , refl
  -- ∈N-unicity InCtxFound InCtxFound = refl , refl
  -- ∈N-unicity InCtxFound (InCtxSkip neq _) = ⊥-elim (neq refl)
  -- ∈N-unicity (InCtxSkip neq _) InCtxFound = ⊥-elim (neq refl)
  -- ∈N-unicity (InCtxSkip neq in-ctx) (InCtxSkip neq' in-ctx') = ∈N-unicity in-ctx in-ctx'

  beyond-▸NTArrow : ∀ {syn syn' t-in t-in' t-out t-out' m m'} ->
    =▷ syn syn' ->
    syn ▸NTArrow t-in , t-out , m -> 
    syn' ▸NTArrow t-in' , t-out' , m' -> 
    (=▷ t-in t-in' × =▷ t-out t-out' × =▷ m m')
  beyond-▸NTArrow =▷★ (NTArrowC _) (NTArrowC _) = =▷★ , =▷★ , =▷★
  beyond-▸NTArrow =▷Refl (NTArrowC match1) (NTArrowC match2) with ▸DTArrow-unicity match1 match2 
  ... | refl , refl , refl = =▷Refl , =▷Refl , =▷Refl

  beyond-▸NTProj : ∀ {syn syn' s t t' m m'} ->
    =▷ syn syn' ->
    syn , s ▸NTProj t , m -> 
    syn' , s ▸NTProj t' , m' -> 
    (=▷ t t' × =▷ m m')
  beyond-▸NTProj =▷★ (NTProjC x) (NTProjC x₁) = =▷★ , =▷★
  beyond-▸NTProj =▷Refl (NTProjC x) (NTProjC x₁) with ▸DTProj-unicity x x₁ 
  ... | refl , refl = =▷Refl , =▷Refl

  beyond-▸NTForall : ∀ {syn syn' x x' t-body t-body' m m'} ->
    =▷ syn syn' ->
    syn ▸NTForall x , t-body , m -> 
    syn' ▸NTForall x' , t-body' , m' -> 
    ((x ≡ x' + (proj₂ t-body') ≡ ★) × =▷ t-body t-body' × =▷ m m')
  beyond-▸NTForall =▷★ (NTForallC _) (NTForallC _) = Inr refl , =▷★ , =▷★
  beyond-▸NTForall =▷Refl (NTForallC match1) (NTForallC match2) with ▸DTForall-unicity match1 match2 
  ... | refl , refl , refl = Inl refl , =▷Refl , =▷Refl

  beyond-NSub : ∀ {t t' d1 d1' d2 d2' x x'} ->
    (x ≡ x' + (proj₂ d1') ≡ ★) ->
    =▷ t t' ->
    =▷ d1 d1' ->
    NSub t x d1 d2  -> 
    NSub t' x' d1' d2'  -> 
    (=▷ d2 d2')
  beyond-NSub _ =▷★ _ (NSub-pair x) (NSub-pair x₁) = =▷★
  beyond-NSub _ =▷Refl =▷★ (NSub-pair x) (NSub-pair x₁) = =▷★-max-r
  beyond-NSub (Inl refl) =▷Refl =▷Refl (NSub-pair x) (NSub-pair x₁) with DSub-unicity x x₁
  ... | refl = =▷Refl
  beyond-NSub (Inr refl) =▷Refl =▷Refl (NSub-pair x) (NSub-pair x₁) = =▷★-max-r

  NUnless-dirty : ∀ {d n t} ->
    NUnless (d , n) (t , ★) ≡ (DUnless d t , ★)
  NUnless-dirty {n = n} {t = □} rewrite max-dirty n = refl 
  NUnless-dirty {t = ■ x} = refl  

  NUnless-dirty-▷ : ∀ {d n t d'} ->
    ▷ (NUnless (d , n) (t , ★)) d'
  NUnless-dirty-▷ {d} {n} {t} rewrite NUnless-dirty {d} {n} {t} = ▷Pair ▶★

  beyond-▶ : 
    {A : Set} -> 
    {a a' : ○ A} 
    {b : A} ->
    =▷ a a' ->
    ▶ a b ->
    ▶ a' b 
  beyond-▶ =▷★ consist = ▶★
  beyond-▶ =▷Refl consist = consist

  beyond-▷ : 
    {A : Set} -> 
    {a a' b : ○ A} ->
    =▷ a a' ->
    ▷ a b ->
    ▷ a' b 
  beyond-▷ =▷★ consist = ▷Pair ▶★
  beyond-▷ =▷Refl consist = consist

  beyond-through-~N : ∀ {syn syn' ana m m'} ->
    =▷ syn syn' ->
    syn ~N ana , m -> 
    syn' ~N ana , m' ->
    =▷ m m'
  beyond-through-~N =▷★ consist1 (~N-pair consist2) = =▷★
  beyond-through-~N =▷Refl consist1 consist2 rewrite ~N-unicity consist1 consist2 = =▷Refl

  preservation-lambda-lemma : ∀ {t syn1 syn1' syn2 ana} ->
    =▷ syn1 syn1' ->
    ▷ (NUnless (NArrow t syn1) ana) syn2 ->
    ▷ (NUnless (NArrow t syn1') ana) syn2
  preservation-lambda-lemma {t = t , n} {ana = □ , n-ana} =▷★ (▷Pair consist) rewrite max-dirty n = ▷Pair ▶★
  preservation-lambda-lemma {t = t , n} {ana = ■ ana , n-ana} =▷★ (▷Pair consist) = ▷Pair consist
  preservation-lambda-lemma {t = t , n} =▷Refl consist = consist

  consist-unless-lemma : ∀ {t1 t2 n1 n2 d} ->
    ▷ (NUnless (NArrow (t1 , n1) (t2 , n2)) (d , •))
      (DUnless (DArrow t1 t2) d , ★)
  consist-unless-lemma {d = □} = ▷Pair ▶Same
  consist-unless-lemma {d = ■ d} = ▷Pair ▶•

  consist-unless-prod : ∀ {t1 t2 n1 n2 d} ->
    ▷ (NUnless (NProd (t1 , n1) (t2 , n2)) (d , •))
      (DUnless (DProd t1 t2) d , ★)
  consist-unless-prod {d = □} = ▷Pair ▶Same
  consist-unless-prod {d = ■ d} = ▷Pair ▶•

  consist-unless-new : ∀ {t t1 t2 t3} ->
    ▷ (NUnless t1 t2) t3 ->
    ▷ (NUnless (t , ★) t2) t3
  consist-unless-new {t2 = □ , snd} con = ▷Pair ▶★
  consist-unless-new {t2 = ■ x , snd} (▷Pair con) = ▷Pair con

  preservation-pair-lemma : ∀ {syn1 syn1' syn2 syn2' ana syn-all} ->
    =▷ syn1 syn1' ->
    =▷ syn2 syn2' ->
    ▷ (NUnless (NProd syn1 syn2) ana) syn-all ->
    ▷ (NUnless (NProd syn1' syn2') ana) syn-all
  preservation-pair-lemma {ana = □ , n-ana} =▷★ =▷★ (▷Pair consist) = ▷Pair ▶★
  preservation-pair-lemma {ana = ■ ana , n-ana} =▷★ =▷★ (▷Pair consist) = ▷Pair consist
  preservation-pair-lemma {ana = □ , n-ana} =▷★ =▷Refl (▷Pair consist) = ▷Pair ▶★
  preservation-pair-lemma {ana = ■ ana , n-ana} =▷★ =▷Refl (▷Pair consist) = ▷Pair consist
  preservation-pair-lemma {syn1 = syn1 , n1} {ana = □ , n-ana} =▷Refl =▷★ (▷Pair consist) rewrite max-dirty n1 = ▷Pair ▶★
  preservation-pair-lemma {syn1 = syn1 , n1} {ana = ■ ana , n-ana} =▷Refl =▷★ (▷Pair consist) = ▷Pair consist
  preservation-pair-lemma =▷Refl =▷Refl consist = consist

  preservation-typfun-lemma : ∀ {x syn1 syn1' syn2 ana} ->
    =▷ syn1 syn1' ->
    ▷ (NUnless (NForall x syn1) ana) syn2 ->
    ▷ (NUnless (NForall x syn1') ana) syn2
  preservation-typfun-lemma =▷Refl consist = consist
  preservation-typfun-lemma {ana = □ , n-ana} =▷★ (▷Pair x) = ▷Pair ▶★
  preservation-typfun-lemma {ana = ■ x , n-ana} beyond consist = consist

  beyond-▷-contra : 
    {A : Set} -> 
    {a b b' : ○ A} ->
    ◁▷ b b' ->
    ▷ a b ->
    ▷ a b' 
  beyond-▷-contra ◁▷C (▷Pair consist) = ▷Pair consist

  l-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε A⟦ e-in ⟧C≡ e ->
    ε A⟦ e-in' ⟧C≡ e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  l-env-subsumable (FillAnaEnvFun _) (FillAnaEnvFun _) ()
  l-env-subsumable (FillAnaEnvAp1 _) (FillAnaEnvAp1 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillAnaEnvAp2 _) (FillAnaEnvAp2 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillAnaEnvAsc _) (FillAnaEnvAsc _) SubsumableAsc = SubsumableAsc
  l-env-subsumable (FillAnaEnvProj _) (FillAnaEnvProj _) SubsumableProj = SubsumableProj
  l-env-subsumable (FillAnaEnvPair1 x) (FillAnaEnvPair1 x₁) ()
  l-env-subsumable (FillAnaEnvPair2 x) (FillAnaEnvPair2 x₁) ()
  l-env-subsumable (FillAnaEnvTypFun x) (FillAnaEnvTypFun x₁) ()
  l-env-subsumable (FillAnaEnvTypAp x) (FillAnaEnvTypAp x₁) SubsumableTypAp = SubsumableTypAp

  u-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε S⟦ e-in ⟧C≡ e ->
    ε S⟦ e-in' ⟧C≡ e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  u-env-subsumable (FillSynEnvFun _) (FillSynEnvFun _) ()
  u-env-subsumable (FillSynEnvAp1 _) (FillSynEnvAp1 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillSynEnvAp2 _) (FillSynEnvAp2 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillSynEnvAsc _) (FillSynEnvAsc _) SubsumableAsc = SubsumableAsc
  u-env-subsumable (FillSynEnvProj _) (FillSynEnvProj _) SubsumableProj = SubsumableProj
  u-env-subsumable (FillSynEnvPair1 x) (FillSynEnvPair1 x₁) ()
  u-env-subsumable (FillSynEnvPair2 x) (FillSynEnvPair2 x₁) ()
  u-env-subsumable (FillSynEnvTypFun x) (FillSynEnvTypFun x₁) ()
  u-env-subsumable (FillSynEnvTypAp x) (FillSynEnvTypAp x₁) SubsumableTypAp = SubsumableTypAp

  oldify-syn : ∀ {Γ e t n n'} ->
    Γ S⊢ (e ⇒ (t , n)) ->
    Γ S⊢ (e ⇒ (t , n'))
  oldify-syn (WFConst (▷Pair consist)) = WFConst (▷Pair consist) 
  oldify-syn (WFHole (▷Pair consist)) = WFHole (▷Pair consist)
  oldify-syn (WFAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana) = WFAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana
  oldify-syn (WFVar in-ctx (▷Pair consist)) = WFVar in-ctx (▷Pair consist)
  oldify-syn (WFAsc wf (▷Pair consist-syn) consist-ana ana) = WFAsc wf (▷Pair consist-syn) consist-ana ana
  oldify-syn (WFProj x (▷Pair x₁) x₂ x₃) = WFProj x (▷Pair x₁) x₂ x₃
  oldify-syn (WFTypAp x x₁ x₂ x₃ (▷Pair x₄) x₅) = WFTypAp x x₁ x₂ x₃ (▷Pair x₄) x₅

  oldify-syn-inner : ∀ {Γ e t m n n'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , n')) ->
    Γ L⊢ ((e ⇒ (t , •)) [ ✔ ]⇐ (□ , n'))
  oldify-syn-inner (WFSubsume subsumable (~N-pair consist) consist-m syn) = WFSubsume subsumable (~N-pair ~DVoidR) ▶Same (oldify-syn syn)
  oldify-syn-inner (WFFun wf (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ x₅ x₆ x₇ syn) = WFFun wf (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ (beyond-▷-contra ◁▷C x₅) (~N-pair ~DVoidR) ▶Same syn
  oldify-syn-inner (WFPair (NTProdC DTProdNone) (▷Pair x) (▷Pair x₁) x₃ x₄ x₅ x₆ w w₁) = WFPair (NTProdC DTProdNone) (▷Pair x) (▷Pair x₁) x₃ (beyond-▷-contra ◁▷C x₄) (~N-pair ~DVoidR) ▶Same w w₁
  oldify-syn-inner (WFTypFun (NTForallBindC DTForallBindNone) (▷Pair x) x₂ (▷Pair x₁) x₄ x₅ wf) = WFTypFun (NTForallBindC DTForallBindNone) (▷Pair x) x₂ (▷Pair x₁) (~N-pair ~DVoidR) ▶Same wf

  dirty-syn-inner : ∀ {Γ e n m m' ana t} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ ana) -> 
    Γ L⊢ ((e ⇒ (t , ★)) [ m' ]⇐ ana)
  dirty-syn-inner (WFSubsume x (~N-pair x₁) x₂ x₃) = WFSubsume x (~N-pair x₁) ▶★ (oldify-syn x₃)
  dirty-syn-inner (WFFun wf x x₁ x₂ x₃ x₄ (▷Pair x₅) (~N-pair x₆) x₇ wt) = WFFun wf x x₁ x₂ x₃ x₄ (▷Pair x₅) (~N-pair x₆) ▶★ wt
  dirty-syn-inner (WFPair (NTProdC y) (▷Pair x) (▷Pair x₁) x₃ x₄ (~N-pair x₅) x₆ w w₁) = WFPair (NTProdC y) (▷Pair x) (▷Pair x₁) x₃ (beyond-▷-contra ◁▷C x₄) (~N-pair x₅) ▶★ w w₁
  dirty-syn-inner (WFTypFun (NTForallBindC x) (▷Pair x₁) x₂ (▷Pair x₃) (~N-pair x₄) x₅ wf) = WFTypFun (NTForallBindC x) (▷Pair x₁) x₂ (▷Pair x₃) (~N-pair x₄) ▶★ wf

  dirty-ana : ∀ {Γ e n n' m m' ana t t'} ->
    Γ L⊢ ((e ⇒ (t , n)) [ m ]⇐ ana) -> 
    Γ L⊢ ((e ⇒ (t , n')) [ m' ]⇐ (t' , ★))
  dirty-ana {n' = n'} {t = t} {t' = t'} (WFSubsume {syn-all = syn-all} subsumable consist-t consist-m syn) with ~N-dec (t , n') (t' , ★)
  ... | _ , (~N-pair consist-t') = WFSubsume subsumable (~N-pair consist-t') ▶★-max-r (oldify-syn syn)
  dirty-ana {t = t} {t' = t'} (WFFun {syn-all = syn-all} {syn-body = syn-body , n-body} {t-asc = t-asc , n-asc} wf (NTArrowC _) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ▸NTArrow-dec (t' , ★)
  ... | (t-in , ★) , (t-out , ★) , (m , ★) , NTArrowC marrow with ~N-dec (■ t-asc , n-asc) (t-in , ★) | ~N-dec (t , ★) (t' , ★)
  ... | m' , consist | _ , ~N-pair consist' with dirty-through-~N-left consist 
  ... | _ , refl = WFFun wf (NTArrowC marrow) (■~N-pair consist) (▷Pair ▶★) ▶★ ▶★ NUnless-dirty-▷ (~N-pair consist') ▶★-max-r ana
  dirty-ana {t = t} {t' = t'} (WFPair (NTProdC y) (▷Pair x) (▷Pair x₁) x₃ x₄ (~N-pair x₅) x₆ w w₁) with ▸NTProd-dec (t' , ★)
  ... | (t-fst , ★) , (t-snd , ★) , (m , ★) , NTProdC marrow with ~N-dec (t , ★) (t' , ★)
  ... | _ , ~N-pair consist' = WFPair (NTProdC marrow) (▷Pair ▶★) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair consist') ▶★-max-r w w₁
  dirty-ana {t = t} {t' = t'} (WFTypFun (NTForallBindC x) (▷Pair x₁) x₂ (▷Pair x₃) (~N-pair x₄) x₅ wf) = WFTypFun (NTForallBindC (proj₂ (proj₂ (▸DTForallBind-dec _ _)))) (▷Pair ▶★) ▶★ NUnless-dirty-▷ (~N-pair (proj₂ (~D-dec _ _))) ▶★-max-r wf

  small-dirty-ana : ∀ {Γ e m m' ana t} ->
    Γ L⊢ (e [ m ]⇐ ana) -> 
    Γ L⊢ (e [ m' ]⇐ (t , ★))
  small-dirty-ana {e = e ⇒ (t , n)} ana = dirty-ana ana

  data DirtierCtx : Ctx -> Ctx -> Set where  
    DirtierCtxRefl : ∀{Γ} ->
       DirtierCtx Γ Γ
    DirtierCtxInit : ∀{x t t' Γ} ->
       DirtierCtx (x ∶ (t' , ★) ∷ Γ) (x ∶ t ∷ Γ) 
    DirtierCtxCons : ∀{x t Γ Γ'} ->
       DirtierCtx Γ Γ' -> 
       DirtierCtx (x ∶ t ∷ Γ) (x ∶ t ∷ Γ')
    DirtierCtxTCons : ∀{x Γ Γ'} ->
       DirtierCtx Γ Γ' -> 
       DirtierCtx (x T∷ Γ) (x T∷ Γ')

  DirtierCtxInit? : ∀{x t t' Γ} ->
    DirtierCtx (x ∶ (t' , ★) ∷? Γ) (x ∶ t ∷? Γ)  
  DirtierCtxInit? {BHole} = DirtierCtxRefl
  DirtierCtxInit? {BVar x} = DirtierCtxInit

  DirtierCtxCons? : ∀{x t Γ Γ'} ->
    DirtierCtx Γ Γ' -> 
    DirtierCtx (x ∶ t ∷? Γ) (x ∶ t ∷? Γ')
  DirtierCtxCons? {BHole} dirtier = dirtier 
  DirtierCtxCons? {BVar x} = DirtierCtxCons

  DirtierCtxTCons? : ∀{x Γ Γ'} ->
    DirtierCtx Γ Γ' -> 
    DirtierCtx (x T∷? Γ) (x T∷? Γ')
  DirtierCtxTCons? {BHole} dirtier = dirtier 
  DirtierCtxTCons? {BVar x} = DirtierCtxTCons

  dirtier-ctx-tlookup : ∀{Γ Γ' x m} ->
    DirtierCtx Γ Γ' -> 
    x T∈ Γ' , m ->
    (x T∈ Γ , m)
  dirtier-ctx-tlookup DirtierCtxRefl InCtxEmpty = InCtxEmpty
  dirtier-ctx-tlookup DirtierCtxRefl InCtxFound = InCtxFound
  dirtier-ctx-tlookup DirtierCtxRefl (InCtxSkip in-ctx) = InCtxSkip in-ctx
  dirtier-ctx-tlookup DirtierCtxInit (InCtxSkip in-ctx) = InCtxSkip in-ctx
  dirtier-ctx-tlookup (DirtierCtxCons dirtier) (InCtxSkip in-ctx) = InCtxSkip (dirtier-ctx-tlookup dirtier in-ctx)
  dirtier-ctx-tlookup DirtierCtxRefl (InCtxTSkip x in-ctx) = InCtxTSkip x in-ctx
  dirtier-ctx-tlookup (DirtierCtxTCons dirtier) InCtxFound = InCtxFound
  dirtier-ctx-tlookup (DirtierCtxTCons dirtier) (InCtxTSkip x in-ctx) = InCtxTSkip x (dirtier-ctx-tlookup dirtier in-ctx)
  
  dirtier-ctx-lookup : ∀{Γ Γ' x t m} ->
    DirtierCtx Γ Γ' -> 
    x , t ∈ Γ' , m ->
    ∃[ t' ] (x , t' ∈ Γ , m) × (=▷ t t')
  dirtier-ctx-lookup DirtierCtxRefl in-ctx = _ , in-ctx , =▷Refl
  dirtier-ctx-lookup DirtierCtxInit InCtxFound = _ , InCtxFound , =▷★
  dirtier-ctx-lookup DirtierCtxInit (InCtxSkip x in-ctx) = _ , InCtxSkip x in-ctx , =▷Refl
  dirtier-ctx-lookup (DirtierCtxCons dirtier) InCtxFound = _ , InCtxFound , =▷Refl
  dirtier-ctx-lookup (DirtierCtxCons dirtier) (InCtxSkip x in-ctx) with dirtier-ctx-lookup dirtier in-ctx 
  ... | t' , in-ctx' , beyond = _ , InCtxSkip x in-ctx' , beyond
  dirtier-ctx-lookup (DirtierCtxTCons dirtier) (InCtxTSkip in-ctx) with dirtier-ctx-lookup dirtier in-ctx 
  ... | t' , in-ctx' , beyond = _ , InCtxTSkip in-ctx' , beyond

  dirtier-ctx-t : ∀{Γ Γ' t} ->
    DirtierCtx Γ Γ' -> 
    Γ' T⊢ t ->
    Γ T⊢ t
  dirtier-ctx-t dirtier WFBase = WFBase
  dirtier-ctx-t dirtier WFHole = WFHole
  dirtier-ctx-t dirtier (WFArrow wf wf₁) = WFArrow (dirtier-ctx-t dirtier wf) (dirtier-ctx-t dirtier wf₁)
  dirtier-ctx-t dirtier (WFProd wf wf₁) = WFProd (dirtier-ctx-t dirtier wf) (dirtier-ctx-t dirtier wf₁)
  dirtier-ctx-t dirtier (WFTVar x) = WFTVar (dirtier-ctx-tlookup dirtier x)
  dirtier-ctx-t dirtier (WFForall wf) = WFForall (dirtier-ctx-t (DirtierCtxTCons? dirtier) wf)

  mutual 

    dirtier-ctx-u : ∀{Γ Γ' e} ->
      DirtierCtx Γ Γ' -> 
      Γ' S⊢ e ->
      Γ S⊢ e
    dirtier-ctx-u dirtier (WFConst x) = WFConst x
    dirtier-ctx-u dirtier (WFHole x) = WFHole x
    dirtier-ctx-u dirtier (WFAp x x₁ x₂ x₃ x₄ x₅) = WFAp x x₁ x₂ x₃ (dirtier-ctx-l dirtier x₄) (dirtier-ctx-l dirtier x₅)
    dirtier-ctx-u dirtier (WFAsc wf x x₁ x₂) = WFAsc (dirtier-ctx-t dirtier wf) x x₁ (dirtier-ctx-l dirtier x₂)
    dirtier-ctx-u dirtier (WFVar x x₁) with dirtier-ctx-lookup dirtier x 
    ... | t' , in-ctx' , beyond = WFVar in-ctx' (beyond-▷ beyond x₁)
    dirtier-ctx-u dirtier (WFProj x x₁ x₂ x₃) = WFProj x x₁ x₂ (dirtier-ctx-l dirtier x₃)
    dirtier-ctx-u dirtier (WFTypAp x x₁ x₂ x₃ x₄ x₅) = WFTypAp (dirtier-ctx-t (DirtierCtxTCons? dirtier) x) x₁ x₂ x₃ x₄ (dirtier-ctx-l dirtier x₅)

    dirtier-ctx-l : ∀{Γ Γ' e} ->
      DirtierCtx Γ Γ' -> 
      Γ' L⊢ e ->
      Γ L⊢ e
    dirtier-ctx-l dirtier (WFSubsume x x₁ x₂ x₃) = WFSubsume x x₁ x₂ (dirtier-ctx-u dirtier x₃)
    dirtier-ctx-l dirtier (WFFun {x = x} wf x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ wt) = WFFun (dirtier-ctx-t dirtier wf) x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ (dirtier-ctx-l (DirtierCtxCons? {x} dirtier) wt)
    dirtier-ctx-l dirtier (WFPair x x₁ x₂ x₃ x₄ x₅ x₆ wt wt₁) = WFPair x x₁ x₂ x₃ x₄ x₅ x₆ (dirtier-ctx-l dirtier wt) (dirtier-ctx-l dirtier wt₁)
    dirtier-ctx-l dirtier (WFTypFun x x₁ x₂ x₃ x₄ x₅ wf) = WFTypFun x x₁ x₂ x₃ x₄ x₅ (dirtier-ctx-l (DirtierCtxTCons? dirtier) wf)

  dirty-ctx : ∀{Γ x t t' e} ->  
    (x ∶ t ∷? Γ) L⊢ e ->  
    (x ∶ (t' , ★) ∷? Γ) L⊢ e        
  dirty-ctx {x = x} = dirtier-ctx-l (DirtierCtxInit? {x})  