
open import Prelude
open import Core.Core

module Core.Environment where

  mutual 

    data AnaEnvSyn : Set where 
      AnaEnvSynRec : AnaEnvCon -> ○Data -> AnaEnvSyn

    data AnaEnvCon : Set where 
      AnaEnvFun : Binding -> ○Type -> Mark -> Mark -> AnaEnvAna -> AnaEnvCon 
      AnaEnvAp1 : AnaEnvAna -> Mark -> AnaExp -> AnaEnvCon 
      AnaEnvAp2 : AnaExp -> Mark -> AnaEnvAna -> AnaEnvCon 
      AnaEnvAsc : ○Type -> AnaEnvAna -> AnaEnvCon 
      AnaEnvPair1 : AnaEnvAna -> AnaExp -> Mark -> AnaEnvCon
      AnaEnvPair2 : AnaExp -> AnaEnvAna -> Mark -> AnaEnvCon
      AnaEnvProj : ProdSide -> AnaEnvAna -> Mark -> AnaEnvCon

    data AnaEnvAna : Set where 
      A⊙ : AnaEnvAna
      AnaEnvAnaRec : AnaEnvSyn -> Mark -> ○Data -> AnaEnvAna

  mutual 

    data SynEnvSyn : Set where 
      S⊙ : SynEnvSyn
      SynEnvSynRec : SynEnvCon -> ○Data -> SynEnvSyn

    data SynEnvCon : Set where 
      SynEnvFun : Binding -> ○Type -> Mark -> Mark -> SynEnvAna -> SynEnvCon 
      SynEnvAp1 : SynEnvAna -> Mark -> AnaExp -> SynEnvCon 
      SynEnvAp2 : AnaExp -> Mark -> SynEnvAna -> SynEnvCon 
      SynEnvAsc : ○Type -> SynEnvAna -> SynEnvCon 
      SynEnvPair1 : SynEnvAna -> AnaExp -> Mark -> SynEnvCon
      SynEnvPair2 : AnaExp -> SynEnvAna -> Mark -> SynEnvCon
      SynEnvProj : ProdSide -> SynEnvAna -> Mark -> SynEnvCon

    data SynEnvAna : Set where 
      SynEnvAnaRec : SynEnvSyn -> Mark -> ○Data -> SynEnvAna 

  mutual 
    data _A⟦_⟧S≡_ : (ε : AnaEnvSyn) (e : AnaExp) (e' : SynExp)  -> Set where
      FillAnaEnvSynRec : ∀ {e ε e' syn} ->
        ε A⟦ e ⟧C≡ e' ->
        (AnaEnvSynRec ε syn) A⟦ e ⟧S≡ (e' ⇒ syn)

    data _A⟦_⟧C≡_ : (ε : AnaEnvCon) (e : AnaExp) (e' : ConExp)  -> Set where
      FillAnaEnvFun : ∀ {e ε e' x t m1 m2} ->
        ε A⟦ e ⟧A≡ e' ->
        (AnaEnvFun x t m1 m2 ε) A⟦ e ⟧C≡ (EFun x t m1 m2 e')
      FillAnaEnvAp1 : ∀ {e ε e' e2 m} ->
        ε A⟦ e ⟧A≡ e' ->
        (AnaEnvAp1 ε m e2) A⟦ e ⟧C≡ (EAp e' m e2)
      FillAnaEnvAp2 : ∀ {e ε e' e1 m} ->
        ε A⟦ e ⟧A≡ e' ->
        (AnaEnvAp2 e1 m ε) A⟦ e ⟧C≡ (EAp e1 m e')
      FillAnaEnvAsc : ∀ {e ε e' t} ->
        ε A⟦ e ⟧A≡ e' ->
        (AnaEnvAsc t ε) A⟦ e ⟧C≡ (EAsc t e')
      FillAnaEnvPair1 : ∀ {e ε e' e2 m} ->
        ε A⟦ e ⟧A≡ e' ->
        (AnaEnvPair1 ε e2 m) A⟦ e ⟧C≡ (EPair e' e2 m)
      FillAnaEnvPair2 : ∀ {e ε e' e1 m} ->  
        ε A⟦ e ⟧A≡ e' ->
        (AnaEnvPair2 e1 ε m) A⟦ e ⟧C≡ (EPair e1 e' m)
      FillAnaEnvProj : ∀ {e ε e' s m} ->
        ε A⟦ e ⟧A≡ e' ->
        (AnaEnvProj s ε m) A⟦ e ⟧C≡ (EProj s e' m)

    data _A⟦_⟧A≡_ : (ε : AnaEnvAna) (e : AnaExp) (e' : AnaExp)  -> Set where
      FillA⊙ : ∀ {e} ->
        A⊙ A⟦ e ⟧A≡ e
      FillAnaEnvAnaRec : ∀ {e e' ana m ε} ->
        ε A⟦ e ⟧S≡ e' ->
        AnaEnvAnaRec ε m ana A⟦ e ⟧A≡ (e' [ m ]⇐ ana)

  mutual 
    data _S⟦_⟧S≡_ : (ε : SynEnvSyn) (e : SynExp) (e' : SynExp)  -> Set where
      FillS⊙ : ∀ {e} ->
        S⊙ S⟦ e ⟧S≡ e
      FillSynEnvSynRec : ∀ {e ε e' syn} ->
        ε S⟦ e ⟧C≡ e' ->
        (SynEnvSynRec ε syn) S⟦ e ⟧S≡ (e' ⇒ syn)

    data _S⟦_⟧C≡_ : (ε : SynEnvCon) (e : SynExp) (e' : ConExp)  -> Set where
      FillSynEnvFun : ∀ {e ε e' x t m1 m2} ->
        ε S⟦ e ⟧A≡ e' ->
        (SynEnvFun x t m1 m2 ε) S⟦ e ⟧C≡ (EFun x t m1 m2 e')
      FillSynEnvAp1 : ∀ {e ε e' e2 m} ->
        ε S⟦ e ⟧A≡ e' ->
        (SynEnvAp1 ε m e2) S⟦ e ⟧C≡ (EAp e' m e2)
      FillSynEnvAp2 : ∀ {e ε e' e1 m} ->
        ε S⟦ e ⟧A≡ e' ->
        (SynEnvAp2 e1 m ε) S⟦ e ⟧C≡ (EAp e1 m e')
      FillSynEnvAsc : ∀ {e ε e' t} ->
        ε S⟦ e ⟧A≡ e' ->
        (SynEnvAsc t ε) S⟦ e ⟧C≡ (EAsc t e')
      FillSynEnvPair1 : ∀ {e ε e' e2 m} ->
        ε S⟦ e ⟧A≡ e' ->
        (SynEnvPair1 ε e2 m) S⟦ e ⟧C≡ (EPair e' e2 m)
      FillSynEnvPair2 : ∀ {e ε e' e1 m} ->
        ε S⟦ e ⟧A≡ e' ->
        (SynEnvPair2 e1 ε m) S⟦ e ⟧C≡ (EPair e1 e' m)
      FillSynEnvProj : ∀ {e ε e' s m} ->
        ε S⟦ e ⟧A≡ e' ->
        (SynEnvProj s ε m) S⟦ e ⟧C≡ (EProj s e' m)

    data _S⟦_⟧A≡_ : (ε : SynEnvAna) (e : SynExp) (e' : AnaExp)  -> Set where
      FillSynEnvAnaRec : ∀ {e e' ana m ε} ->
        ε S⟦ e ⟧S≡ e' ->
        SynEnvAnaRec ε m ana S⟦ e ⟧A≡ (e' [ m ]⇐ ana)

  mutual 

    ComposeULU : SynEnvAna -> AnaEnvSyn -> SynEnvSyn
    ComposeULU ε1 (AnaEnvSynRec ε2 t) = SynEnvSynRec (ComposeULM ε1 ε2) t
    
    ComposeULM : SynEnvAna -> AnaEnvCon -> SynEnvCon
    ComposeULM ε1 (AnaEnvFun x t m1 m2 ε2) = SynEnvFun x t m1 m2 (ComposeULL ε1 ε2)
    ComposeULM ε1 (AnaEnvAp1 ε2 m e2) = SynEnvAp1 (ComposeULL ε1 ε2) m e2
    ComposeULM ε1 (AnaEnvAp2 e1 m ε2) = SynEnvAp2 e1 m (ComposeULL ε1 ε2)
    ComposeULM ε1 (AnaEnvAsc t ε2) = SynEnvAsc t (ComposeULL ε1 ε2)
    ComposeULM ε1 (AnaEnvPair1 ε2 e2 m) = SynEnvPair1 (ComposeULL ε1 ε2) e2 m
    ComposeULM ε1 (AnaEnvPair2 e1 ε2 m) = SynEnvPair2 e1 (ComposeULL ε1 ε2) m
    ComposeULM ε1 (AnaEnvProj s ε2 m) = SynEnvProj s (ComposeULL ε1 ε2) m


    ComposeULL : SynEnvAna -> AnaEnvAna -> SynEnvAna 
    ComposeULL ε1 A⊙ = ε1
    ComposeULL ε1 (AnaEnvAnaRec ε2 m ana) = SynEnvAnaRec (ComposeULU ε1 ε2) m ana
  
  mutual 

    ComposeLLU : AnaEnvAna -> AnaEnvSyn -> AnaEnvSyn
    ComposeLLU ε1 (AnaEnvSynRec ε2 t) = AnaEnvSynRec (ComposeLLM ε1 ε2) t
    
    ComposeLLM : AnaEnvAna -> AnaEnvCon -> AnaEnvCon
    ComposeLLM ε1 (AnaEnvFun x t m1 m2 ε2) = AnaEnvFun x t m1 m2 (ComposeLLL ε1 ε2)
    ComposeLLM ε1 (AnaEnvAp1 ε2 m e2) = AnaEnvAp1 (ComposeLLL ε1 ε2) m e2
    ComposeLLM ε1 (AnaEnvAp2 e1 m ε2) = AnaEnvAp2 e1 m (ComposeLLL ε1 ε2)
    ComposeLLM ε1 (AnaEnvAsc t ε2) = AnaEnvAsc t (ComposeLLL ε1 ε2)
    ComposeLLM ε1 (AnaEnvPair1 ε2 e2 m) = AnaEnvPair1 (ComposeLLL ε1 ε2) e2 m
    ComposeLLM ε1 (AnaEnvPair2 e1 ε2 m) = AnaEnvPair2 e1 (ComposeLLL ε1 ε2) m
    ComposeLLM ε1 (AnaEnvProj s ε2 m) = AnaEnvProj s (ComposeLLL ε1 ε2) m

    ComposeLLL : AnaEnvAna -> AnaEnvAna -> AnaEnvAna 
    ComposeLLL ε1 A⊙ = ε1
    ComposeLLL ε1 (AnaEnvAnaRec ε2 m ana) = AnaEnvAnaRec (ComposeLLU ε1 ε2) m ana
  
  mutual 

    ComposeUUU : SynEnvSyn -> SynEnvSyn -> SynEnvSyn
    ComposeUUU ε1 S⊙ = ε1
    ComposeUUU ε1 (SynEnvSynRec ε2 t) = SynEnvSynRec (ComposeUUM ε1 ε2) t
    
    ComposeUUM : SynEnvSyn -> SynEnvCon -> SynEnvCon
    ComposeUUM ε1 (SynEnvFun x t m1 m2 ε2) = SynEnvFun x t m1 m2 (ComposeUUL ε1 ε2)
    ComposeUUM ε1 (SynEnvAp1 ε2 m e2) = SynEnvAp1 (ComposeUUL ε1 ε2) m e2
    ComposeUUM ε1 (SynEnvAp2 e1 m ε2) = SynEnvAp2 e1 m (ComposeUUL ε1 ε2)
    ComposeUUM ε1 (SynEnvAsc t ε2) = SynEnvAsc t (ComposeUUL ε1 ε2)
    ComposeUUM ε1 (SynEnvPair1 ε2 e2 m) = SynEnvPair1 (ComposeUUL ε1 ε2) e2 m
    ComposeUUM ε1 (SynEnvPair2 e1 ε2 m) = SynEnvPair2 e1 (ComposeUUL ε1 ε2) m
    ComposeUUM ε1 (SynEnvProj s ε2 m) = SynEnvProj s (ComposeUUL ε1 ε2) m

    ComposeUUL : SynEnvSyn -> SynEnvAna -> SynEnvAna 
    ComposeUUL ε1 (SynEnvAnaRec ε2 m ana) = SynEnvAnaRec (ComposeUUU ε1 ε2) m ana
  
  mutual 

    ComposeLUU : AnaEnvSyn -> SynEnvSyn -> AnaEnvSyn
    ComposeLUU ε1 S⊙ = ε1
    ComposeLUU ε1 (SynEnvSynRec ε2 t) = AnaEnvSynRec (ComposeLUM ε1 ε2) t
    
    ComposeLUM : AnaEnvSyn -> SynEnvCon -> AnaEnvCon
    ComposeLUM ε1 (SynEnvFun x t m1 m2 ε2) = AnaEnvFun x t m1 m2 (ComposeLUL ε1 ε2)
    ComposeLUM ε1 (SynEnvAp1 ε2 m e2) = AnaEnvAp1 (ComposeLUL ε1 ε2) m e2
    ComposeLUM ε1 (SynEnvAp2 e1 m ε2) = AnaEnvAp2 e1 m (ComposeLUL ε1 ε2)
    ComposeLUM ε1 (SynEnvAsc t ε2) = AnaEnvAsc t (ComposeLUL ε1 ε2)
    ComposeLUM ε1 (SynEnvPair1 ε2 e2 m) = AnaEnvPair1 (ComposeLUL ε1 ε2) e2 m
    ComposeLUM ε1 (SynEnvPair2 e1 ε2 m) = AnaEnvPair2 e1 (ComposeLUL ε1 ε2) m
    ComposeLUM ε1 (SynEnvProj s ε2 m) = AnaEnvProj s (ComposeLUL ε1 ε2) m

    ComposeLUL : AnaEnvSyn -> SynEnvAna -> AnaEnvAna 
    ComposeLUL ε1 (SynEnvAnaRec ε2 m ana) = AnaEnvAnaRec (ComposeLUU ε1 ε2) m ana

  mutual 

    FillULU : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 S⟦ e1 ⟧A≡ e2 -> 
      ε2 A⟦ e2 ⟧S≡ e3 ->
      (ComposeULU ε1 ε2) S⟦ e1 ⟧S≡ e3
    FillULU fill1 (FillAnaEnvSynRec fill2) = FillSynEnvSynRec (FillULM fill1 fill2)

    FillULM : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 S⟦ e1 ⟧A≡ e2 -> 
      ε2 A⟦ e2 ⟧C≡ e3 ->
      (ComposeULM ε1 ε2) S⟦ e1 ⟧C≡ e3
    FillULM fill1 (FillAnaEnvFun fill2) = FillSynEnvFun (FillULL fill1 fill2)
    FillULM fill1 (FillAnaEnvAp1 fill2) = FillSynEnvAp1 (FillULL fill1 fill2)
    FillULM fill1 (FillAnaEnvAp2 fill2) = FillSynEnvAp2 (FillULL fill1 fill2)
    FillULM fill1 (FillAnaEnvAsc fill2) = FillSynEnvAsc (FillULL fill1 fill2)
    FillULM fill1 (FillAnaEnvPair1 fill2) = FillSynEnvPair1 (FillULL fill1 fill2)
    FillULM fill1 (FillAnaEnvPair2 fill2) = FillSynEnvPair2 (FillULL fill1 fill2)
    FillULM fill1 (FillAnaEnvProj fill2) = FillSynEnvProj (FillULL fill1 fill2)

    FillULL : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 S⟦ e1 ⟧A≡ e2 -> 
      ε2 A⟦ e2 ⟧A≡ e3 -> 
      (ComposeULL ε1 ε2) S⟦ e1 ⟧A≡ e3
    FillULL fill1 FillA⊙ = fill1 
    FillULL fill1 (FillAnaEnvAnaRec fill2) = FillSynEnvAnaRec (FillULU fill1 fill2)
  
  mutual 

    FillLLU : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 A⟦ e1 ⟧A≡ e2 -> 
      ε2 A⟦ e2 ⟧S≡ e3 ->
      (ComposeLLU ε1 ε2) A⟦ e1 ⟧S≡ e3
    FillLLU fill1 (FillAnaEnvSynRec fill2) = FillAnaEnvSynRec (FillLLM fill1 fill2)

    FillLLM : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 A⟦ e1 ⟧A≡ e2 -> 
      ε2 A⟦ e2 ⟧C≡ e3 ->
      (ComposeLLM ε1 ε2) A⟦ e1 ⟧C≡ e3
    FillLLM fill1 (FillAnaEnvFun fill2) = FillAnaEnvFun (FillLLL fill1 fill2)
    FillLLM fill1 (FillAnaEnvAp1 fill2) = FillAnaEnvAp1 (FillLLL fill1 fill2)
    FillLLM fill1 (FillAnaEnvAp2 fill2) = FillAnaEnvAp2 (FillLLL fill1 fill2)
    FillLLM fill1 (FillAnaEnvAsc fill2) = FillAnaEnvAsc (FillLLL fill1 fill2)
    FillLLM fill1 (FillAnaEnvPair1 fill2) = FillAnaEnvPair1 (FillLLL fill1 fill2)
    FillLLM fill1 (FillAnaEnvPair2 fill2) = FillAnaEnvPair2 (FillLLL fill1 fill2)
    FillLLM fill1 (FillAnaEnvProj fill2) = FillAnaEnvProj (FillLLL fill1 fill2)

    FillLLL : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 A⟦ e1 ⟧A≡ e2 -> 
      ε2 A⟦ e2 ⟧A≡ e3 -> 
      (ComposeLLL ε1 ε2) A⟦ e1 ⟧A≡ e3
    FillLLL fill1 FillA⊙ = fill1 
    FillLLL fill1 (FillAnaEnvAnaRec fill2) = FillAnaEnvAnaRec (FillLLU fill1 fill2)

  mutual 

    FillUUU : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 S⟦ e1 ⟧S≡ e2 -> 
      ε2 S⟦ e2 ⟧S≡ e3 ->
      (ComposeUUU ε1 ε2) S⟦ e1 ⟧S≡ e3
    FillUUU fill1 FillS⊙ = fill1 
    FillUUU fill1 (FillSynEnvSynRec fill2) = FillSynEnvSynRec (FillUUM fill1 fill2)

    FillUUM : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 S⟦ e1 ⟧S≡ e2 -> 
      ε2 S⟦ e2 ⟧C≡ e3 ->
      (ComposeUUM ε1 ε2) S⟦ e1 ⟧C≡ e3
    FillUUM fill1 (FillSynEnvFun fill2) = FillSynEnvFun (FillUUL fill1 fill2)
    FillUUM fill1 (FillSynEnvAp1 fill2) = FillSynEnvAp1 (FillUUL fill1 fill2)
    FillUUM fill1 (FillSynEnvAp2 fill2) = FillSynEnvAp2 (FillUUL fill1 fill2)
    FillUUM fill1 (FillSynEnvAsc fill2) = FillSynEnvAsc (FillUUL fill1 fill2)
    FillUUM fill1 (FillSynEnvPair1 fill2) = FillSynEnvPair1 (FillUUL fill1 fill2)
    FillUUM fill1 (FillSynEnvPair2 fill2) = FillSynEnvPair2 (FillUUL fill1 fill2)
    FillUUM fill1 (FillSynEnvProj fill2) = FillSynEnvProj (FillUUL fill1 fill2)

    FillUUL : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 S⟦ e1 ⟧S≡ e2 -> 
      ε2 S⟦ e2 ⟧A≡ e3 -> 
      (ComposeUUL ε1 ε2) S⟦ e1 ⟧A≡ e3
    FillUUL fill1 (FillSynEnvAnaRec fill2) = FillSynEnvAnaRec (FillUUU fill1 fill2)

  mutual 

    FillLUU : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 A⟦ e1 ⟧S≡ e2 -> 
      ε2 S⟦ e2 ⟧S≡ e3 ->
      (ComposeLUU ε1 ε2) A⟦ e1 ⟧S≡ e3
    FillLUU fill1 FillS⊙ = fill1 
    FillLUU fill1 (FillSynEnvSynRec fill2) = FillAnaEnvSynRec (FillLUM fill1 fill2)

    FillLUM : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 A⟦ e1 ⟧S≡ e2 -> 
      ε2 S⟦ e2 ⟧C≡ e3 ->
      (ComposeLUM ε1 ε2) A⟦ e1 ⟧C≡ e3
    FillLUM fill1 (FillSynEnvFun fill2) = FillAnaEnvFun (FillLUL fill1 fill2)
    FillLUM fill1 (FillSynEnvAp1 fill2) = FillAnaEnvAp1 (FillLUL fill1 fill2)
    FillLUM fill1 (FillSynEnvAp2 fill2) = FillAnaEnvAp2 (FillLUL fill1 fill2)
    FillLUM fill1 (FillSynEnvAsc fill2) = FillAnaEnvAsc (FillLUL fill1 fill2)
    FillLUM fill1 (FillSynEnvPair1 fill2) = FillAnaEnvPair1 (FillLUL fill1 fill2)
    FillLUM fill1 (FillSynEnvPair2 fill2) = FillAnaEnvPair2 (FillLUL fill1 fill2)
    FillLUM fill1 (FillSynEnvProj fill2) = FillAnaEnvProj (FillLUL fill1 fill2)

    FillLUL : ∀ {ε1 ε2 e1 e2 e3} ->
      ε1 A⟦ e1 ⟧S≡ e2 -> 
      ε2 S⟦ e2 ⟧A≡ e3 -> 
      (ComposeLUL ε1 ε2) A⟦ e1 ⟧A≡ e3
    FillLUL fill1 (FillSynEnvAnaRec fill2) = FillAnaEnvAnaRec (FillLUU fill1 fill2)