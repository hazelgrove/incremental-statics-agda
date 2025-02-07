
open import Data.Nat hiding (_+_; _⊓_)
open import Data.Unit 
open import Data.Empty 
open import Data.Bool hiding (_<_; _≟_)
open import Data.Sum renaming (_⊎_ to _+_; inj₁ to Inl ; inj₂ to Inr) hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Prelude

open import Core.Core
open import Core.Environment
open import Core.WellTyped

module Core.Lemmas-Preservation where

  -- oldify-ntmatch : ∀ {t n t1 t2 m n1 n2 n3} ->
  --   (t , n) ▸NTArrow (t1 , n1) , (t2 , n2) , (m , n3) ->
  --   (t , Old) ▸NTArrow (t1 , Old) , (t2 , Old) , (m , MarkOld)
  -- oldify-ntmatch (MNTArrowOldMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowOldNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch (MNTArrowNewMatch m) = MNTArrowOldMatch m
  -- oldify-ntmatch (MNTArrowNewNoMatch m) = MNTArrowOldNoMatch m
  -- oldify-ntmatch MNTArrowArrow = MNTArrowOldMatch MArrowArrow

  -- the "beyondness" relation - the latter is the unchanged or [New]
  data =▷ {A : Set} : NEW A -> NEW A -> Set where 
    =▷New : ∀ {s t} -> 
      =▷ s (t , New)
    =▷Refl : ∀ {s} -> 
      =▷ s s

  -- stays the same, or becomes old
  data ◁= {A : Set} : NEW A -> NEW A -> Set where 
    ◁=Old : ∀ {t t' n} -> 
      ◁= (t , n) (t' , Old)
    ◁=Refl : ∀ {t} -> ◁= t t

  data ◁▷ {A : Set} : NEW A -> NEW A -> Set where 
    ◁▷C : ∀ {t n n'} -> 
      ◁▷ (t , n) (t , n')

  max-new : (n : Newness) -> n ⊓ New ≡ New 
  max-new Old = refl
  max-new New = refl

  max-old : (n : Newness) -> n ⊓ Old ≡ n 
  max-old Old = refl
  max-old New = refl

  ~DVoid-left : ∀ {t m} ->
    t ~D □ , m ->
    m ≡ ✔
  ~DVoid-left ~DVoidL = refl
  ~DVoid-left ~DVoidR = refl

  ~D-unless : ∀ {t1 t2} ->
    DUnless t1 t2 ~D t2 , ✔
  ~D-unless {t2 = □} = ~DVoidR
  ~D-unless {t2 = ■ x} = ~DVoidL 

  -- -- ▷D-new : ∀ {t syn} -> ▷D (■ (t , New)) syn
  -- -- ▷D-new {syn = □} = ▷DVoidR
  -- -- ▷D-new {syn = ■ (t , n)} = ▷DSome MergeInfoNew

  -- new-through-▸DTArrow : ∀ {t t-in t-out m} ->
  --   ■ (t , New) ▸DTArrow t-in , t-out , m -> 
  --   ∃[ t-in' ] ∃[ t-out' ] ∃[ m' ] (t-in ≡ (t-in' , New) × t-out ≡ (t-out' , New) × m ≡ (m' , New))
  -- new-through-▸DTArrow (SynArrowSome (MNTArrowNew x)) = _ , _ , _ , refl , refl , refl

  new-through-~N-left : ∀ {d t m} ->
    d ~N (t , New) , m -> 
    ∃[ m' ] m ≡ (m' , New)
  new-through-~N-left (~N-pair {n1 = n1} consist) rewrite max-new n1 = _ , refl

  new-through-~N-right : ∀ {d t m} ->
    (t , New) ~N d , m -> 
    ∃[ m' ] m ≡ (m' , New)
  new-through-~N-right (~N-pair consist) = _ , refl

  ▶Same : ∀ {n} ->
    {A : Set} ->
    {a : A} ->
    ▶ (a , n) a
  ▶Same {Old} = ▶Old
  ▶Same {New} = ▶New

  ▶New-max-r : ∀ {n} -> 
    {A : Set} -> 
    {a a' : A} ->
    ▶ (a , (n ⊓ New)) a'
  ▶New-max-r {n = n} rewrite max-new n = ▶New

  -- new-through-~D-right : ∀ {d t m} ->
  --   ■ (t , New) ~D d , m -> 
  --   ∃[ m' ] m ≡ (m' , New)
  -- new-through-~D-right ~DVoidR = ✔ , refl
  -- new-through-~D-right (~DSome (NMConsist {n1 = n1} x)) = _ , refl

  ▸TArrow-dec : 
    (t : Type) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸TArrow t-in , t-out , m
  ▸TArrow-dec TBase = THole , THole , ✖ , MArrowBase
  ▸TArrow-dec THole = THole , THole , ✔ , MArrowHole
  ▸TArrow-dec (TArrow t1 t2) = t1 , t2 , ✔ , MArrowArrow

  ▸DTArrow-dec : 
    (t : Data) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] t ▸DTArrow t-in , t-out , m
  ▸DTArrow-dec □ = □ , □ , ✔ , DTArrowNone
  ▸DTArrow-dec (■ t) with ▸TArrow-dec t 
  ... | t1 , t2 , m , match = ■ t1 , ■ t2 , m , DTArrowSome match

  ▸NTArrow-dec : 
    (d : NewData) -> 
    ∃[ t-in ] ∃[ t-out ] ∃[ m ] d ▸NTArrow t-in , t-out , m
  ▸NTArrow-dec (d , n) with ▸DTArrow-dec d 
  ... | t1 , t2 , m , match = (t1 , n) , (t2 , n) , (m , n) , NTArrowC match

  ~-dec : 
    (syn ana : Type) -> 
    ∃[ m ] syn ~ ana , m 
  ~-dec TBase TBase = ✔ , ConsistBase
  ~-dec TBase THole = ✔ , ConsistHoleR
  ~-dec TBase (TArrow _ _) = ✖ , InconsistBaseArr
  ~-dec THole TBase = ✔ , ConsistHoleL
  ~-dec THole THole = ✔ , ConsistHoleR
  ~-dec THole (TArrow _ _) = ✔ , ConsistHoleL
  ~-dec (TArrow _ _) TBase = ✖ , InconsistArrBase
  ~-dec (TArrow _ _) THole = ✔ , ConsistHoleR
  ~-dec (TArrow syn1 syn2) (TArrow ana1 ana2) with ~-dec syn1 ana1 | ~-dec syn2 ana2 
  ... | m1 , consist1 | m2 , consist2 = (m1 ⊓M m2) , ConsistArr consist1 consist2

  ~D-dec : 
    (syn ana : Data) -> 
    ∃[ m ] syn ~D ana , m 
  ~D-dec □ _ = ✔ , ~DVoidL
  ~D-dec (■ syn) □ = ✔ , ~DVoidR
  ~D-dec (■ syn) (■ ana) with ~-dec syn ana 
  ... | m , consist = m , (~DSome consist)

  ~N-dec : 
    (syn ana : NewData) -> 
    ∃[ m ] syn ~N ana , m 
  ~N-dec (syn-d , syn-n) (ana-d , ana-n) with ~D-dec syn-d ana-d
  ... | m , consist = (m , (syn-n ⊓ ana-n)) , ~N-pair consist

  ▸TArrow-unicity : ∀ {t t-in t-in' t-out t-out' m m'} ->
    t ▸TArrow t-in , t-out , m -> 
    t ▸TArrow t-in' , t-out' , m' -> 
    (t-in ≡ t-in' × t-out ≡ t-out' × m ≡ m')
  ▸TArrow-unicity MArrowBase MArrowBase = refl , refl , refl
  ▸TArrow-unicity MArrowHole MArrowHole = refl , refl , refl
  ▸TArrow-unicity MArrowArrow MArrowArrow = refl , refl , refl

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

  ~-unicity : ∀ {syn ana m m'} ->
    syn ~ ana , m -> 
    syn ~ ana , m' ->
    m ≡ m'
  ~-unicity ConsistBase ConsistBase = refl
  ~-unicity ConsistHoleL ConsistHoleL = refl
  ~-unicity ConsistHoleL ConsistHoleR = refl
  ~-unicity ConsistHoleR ConsistHoleL = refl
  ~-unicity ConsistHoleR ConsistHoleR = refl
  ~-unicity InconsistBaseArr InconsistBaseArr = refl
  ~-unicity InconsistArrBase InconsistArrBase = refl
  ~-unicity (ConsistArr con1 con2) (ConsistArr con3 con4) 
    rewrite ~-unicity con1 con3 
    rewrite ~-unicity con2 con4 = refl

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

  ∈N-unicity : ∀ {x t t' Γ m m'} ->
    x , t ∈N Γ , m ->
    x , t' ∈N Γ , m' ->
    (t ≡ t' × m ≡ m')
  ∈N-unicity InCtxEmpty InCtxEmpty = refl , refl
  ∈N-unicity InCtxFound InCtxFound = refl , refl
  ∈N-unicity InCtxFound (InCtxSkip neq _) = ⊥-elim (neq refl)
  ∈N-unicity (InCtxSkip neq _) InCtxFound = ⊥-elim (neq refl)
  ∈N-unicity (InCtxSkip neq in-ctx) (InCtxSkip neq' in-ctx') = ∈N-unicity in-ctx in-ctx'

  beyond-▸NTArrow : ∀ {syn syn' t-in t-in' t-out t-out' m m'} ->
    =▷ syn syn' ->
    syn ▸NTArrow t-in , t-out , m -> 
    syn' ▸NTArrow t-in' , t-out' , m' -> 
    (=▷ t-in t-in' × =▷ t-out t-out' × =▷ m m')
  beyond-▸NTArrow =▷New (NTArrowC _) (NTArrowC _) = =▷New , =▷New , =▷New
  beyond-▸NTArrow =▷Refl (NTArrowC match1) (NTArrowC match2) with ▸DTArrow-unicity match1 match2 
  ... | refl , refl , refl = =▷Refl , =▷Refl , =▷Refl

  NUnless-new : ∀ {d n t} ->
    NUnless (d , n) (t , New) ≡ (DUnless d t , New)
  NUnless-new {n = n} {t = □} rewrite max-new n = refl 
  NUnless-new {t = ■ x} = refl  

  NUnless-new-▶ : ∀ {d n t d'} ->
    ▷ (NUnless (d , n) (t , New)) d'
  NUnless-new-▶ {d} {n} {t} rewrite NUnless-new {d} {n} {t} = ▷Pair ▶New

  -- beyond-consist-m : ∀ {m1 m1' m2} ->
  --   =▷M m1 m1' ->
  --   ▷NM m1 m2 ->
  --   ▷NM m1' m2 
  -- beyond-consist-m =▷MNew consist = ▷NMNew
  -- beyond-consist-m ▷MRefl consist = consist

  beyond-▶ : 
    {A : Set} -> 
    {a a' : NEW A} 
    {b : A} ->
    =▷ a a' ->
    ▶ a b ->
    ▶ a' b 
  beyond-▶ =▷New consist = ▶New
  beyond-▶ =▷Refl consist = consist

  beyond-▷ : 
    {A : Set} -> 
    {a a' b : NEW A} ->
    =▷ a a' ->
    ▷ a b ->
    ▷ a' b 
  beyond-▷ =▷New consist = ▷Pair ▶New
  beyond-▷ =▷Refl consist = consist

  -- -- new-beyond-through-~NM : ∀ {syn syn' ana m m'} ->
  -- --   =▷T syn syn' ->
  -- --   (t , New) ~NM ana , m -> 
  -- --   (t , Old) ~NM ana , m' ->
  -- --   =▷M m m'
  -- -- beyond-through-~NM = {!   !}

  beyond-through-~N : ∀ {syn syn' ana m m'} ->
    =▷ syn syn' ->
    syn ~N ana , m -> 
    syn' ~N ana , m' ->
    =▷ m m'
  beyond-through-~N =▷New consist1 consist2 with new-through-~N-right consist2 
  ... | m' , refl = =▷New
  beyond-through-~N =▷Refl consist1 consist2 rewrite ~N-unicity consist1 consist2 = =▷Refl

  preservation-lambda-lemma : ∀ {t syn1 syn1' syn2} ->
    =▷ syn1 syn1' ->
    ▷ (NArrow t syn1) syn2 ->
    ▷ (NArrow t syn1') syn2
  preservation-lambda-lemma {t = t , n} =▷New (▷Pair consist) rewrite max-new n = ▷Pair ▶New
  preservation-lambda-lemma =▷Refl consist = consist

  preservation-lambda-lemma-2 : ∀ {t1 t2 n syn} ->
    =▷ ((■ t2 , n)) syn -> 
    ▷ (NArrow (t1 , Old) syn) ((■ (TArrow t1 t2) , New))
  preservation-lambda-lemma-2 =▷New = ▷Pair ▶New 
  preservation-lambda-lemma-2 =▷Refl = ▷Pair ▶Same 

  preservation-lambda-lemma-3 : ∀ {t syn1 syn1' syn2 ana} ->
    =▷ syn1 syn1' ->
    ▷ (NUnless (NArrow t syn1) ana) syn2 ->
    ▷ (NUnless (NArrow t syn1') ana) syn2
  preservation-lambda-lemma-3 {t = t , n} {ana = □ , n-ana} =▷New (▷Pair consist) rewrite max-new n = ▷Pair ▶New
  preservation-lambda-lemma-3 {t = t , n} {ana = ■ ana , n-ana} =▷New (▷Pair consist) = ▷Pair consist
  preservation-lambda-lemma-3 {t = t , n} =▷Refl consist = consist

  consist-unless-lemma : ∀ {t1 t2 n1 n2 d} ->
    ▷ (NUnless (NArrow (t1 , n1) (t2 , n2)) (d , Old))
      (DUnless (DArrow t1 t2) d , New)
  consist-unless-lemma {d = □} = ▷Pair ▶Same
  consist-unless-lemma {d = ■ d} = ▷Pair ▶Old

  beyond-▷-contra : 
    {A : Set} -> 
    {a b b' : NEW A} ->
    ◁▷ b b' ->
    ▷ a b ->
    ▷ a b' 
  beyond-▷-contra ◁▷C (▷Pair consist) = ▷Pair consist

  beyond-▷■-contra : 
    {A : Set} -> 
    {a : NEW A} ->
    {b b' : NEW (DATA A)} ->
    ◁▷ b b' ->
    ▷■ a b ->
    ▷■ a b' 
  beyond-▷■-contra ◁▷C (▷■Pair (▷Pair consist)) = ▷■Pair (▷Pair consist)

  l-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε L⟦ e-in ⟧Mid== e ->
    ε L⟦ e-in' ⟧Mid== e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  l-env-subsumable (FillLEnvFun _) (FillLEnvFun _) ()
  l-env-subsumable (FillLEnvAp1 _) (FillLEnvAp1 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillLEnvAp2 _) (FillLEnvAp2 _) SubsumableAp = SubsumableAp
  l-env-subsumable (FillLEnvAsc _) (FillLEnvAsc _) SubsumableAsc = SubsumableAsc

  u-env-subsumable : ∀ {ε e e' e-in e-in'} -> 
    ε U⟦ e-in ⟧Mid== e ->
    ε U⟦ e-in' ⟧Mid== e' ->
    SubsumableMid e -> 
    SubsumableMid e'
  u-env-subsumable (FillUEnvFun _) (FillUEnvFun _) ()
  u-env-subsumable (FillUEnvAp1 _) (FillUEnvAp1 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillUEnvAp2 _) (FillUEnvAp2 _) SubsumableAp = SubsumableAp
  u-env-subsumable (FillUEnvAsc _) (FillUEnvAsc _) SubsumableAsc = SubsumableAsc

  oldify-syn : ∀ {Γ e t n} ->
    Γ ⊢ e ⇒ (t , n) ⇒ ->
    Γ ⊢ e ⇒ (t , Old) ⇒
  oldify-syn (SynConst (▷Pair consist)) = SynConst (▷Pair consist) 
  oldify-syn (SynHole (▷Pair consist)) = SynHole (▷Pair consist)
  oldify-syn (SynAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana) = SynAp marrow (▷Pair consist-syn) consist-ana consist-mark syn ana
  oldify-syn (SynVar in-ctx (▷■Pair (▷Pair consist))) = SynVar in-ctx (▷■Pair (▷Pair consist)) 
  oldify-syn (SynAsc (▷■Pair (▷Pair consist-syn)) consist-ana ana) = SynAsc (▷■Pair (▷Pair consist-syn)) consist-ana ana

  oldify-syn-inner : ∀ {Γ e t m n} ->
    Γ ⊢ ((e ⇒ (t , n)) [ m ]⇐ (□ , Old)) ⇐ ->
    Γ ⊢ ((e ⇒ (t , Old)) [ ✔ ]⇐ (□ , Old)) ⇐
  oldify-syn-inner (AnaSubsume subsumable (~N-pair consist) consist-m syn) = AnaSubsume subsumable (~N-pair ~DVoidR) ▶Old (oldify-syn syn) 
  oldify-syn-inner (AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ x₅ x₆ x₇ syn) = AnaFun (NTArrowC DTArrowNone) (■~N-pair (~N-pair ~DVoidR)) x₂ x₃ x₄ (beyond-▷-contra ◁▷C x₅) (~N-pair ~DVoidR) ▶Old syn

  newify-ana : ∀ {Γ e m ana t} ->
    Γ ⊢ e [ m ]⇐ ana ⇐ -> 
    Γ ⊢ e [ m ]⇐ (t , New) ⇐
  newify-ana {t = t} (AnaSubsume {syn-all = syn-all} subsumable consist-t consist-m syn) with ~N-dec syn-all ((t , New)) 
  ... | _ , consist-t' with new-through-~N-left consist-t' 
  ... | _ , refl = AnaSubsume subsumable consist-t' ▶New syn
  newify-ana {t = t-ana'} (AnaFun {syn-all = syn-all} {syn-body = syn-body , n-body} {t-asc = t-asc , n-asc} (NTArrowC marrow) (■~N-pair (~N-pair consist)) consist-ana consist-asc consist-body consist-syn consist-all consist-m-all ana) with ▸DTArrow-dec t-ana' | ~N-dec syn-all (t-ana' , New )
  ... | t-in-ana' , t-out-ana' , m-ana-ana' , marrow' | _ , consist-syn' with ~D-dec (■ t-asc) t-in-ana' | new-through-~N-left consist-syn' 
  ... | _ , consist' | _ , refl rewrite max-new (n-asc ⊓ n-body) = AnaFun (NTArrowC marrow') (■~N-pair (~N-pair consist')) (▷Pair ▶New) ▶New ▶New-max-r NUnless-new-▶ consist-syn' ▶New ana 
    where 
    consist-helper : ∀ {t} -> ▷ (t , ((n-asc ⊓ n-body) ⊓ New)) syn-all 
    consist-helper rewrite max-new (n-asc ⊓ n-body) = ▷Pair ▶New