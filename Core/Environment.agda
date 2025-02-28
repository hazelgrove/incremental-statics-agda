
open import Prelude
open import Core.Core

module Core.Environment where

  mutual 

    -- data LEnvUp : Set where 
    --   LEnvUpRec : LEnvMid -> NewData -> LEnvUp

    data LEnvMid : Set where 
      LEnvFun : Binding -> NewType -> Mark -> Mark -> LEnvLow -> LEnvMid 
      LEnvAp1 : LEnvLow -> Mark -> ExpLow -> LEnvMid 
      LEnvAp2 : ExpLow -> Mark -> LEnvLow -> LEnvMid 
      LEnvAsc : NewType -> LEnvLow -> LEnvMid 

    data LEnvLow : Set where 
      L⊙ : LEnvLow
      LEnvLowRec : NewData -> LEnvMid -> NewData -> Mark -> LEnvLow

  -- mutual 

  --   data UEnvUp : Set where 
  --     U⊙ : UEnvUp
  --     UEnvUpRec : UEnvMid -> NewData -> UEnvUp

  --   data UEnvMid : Set where 
  --     UEnvFun : Binding -> NewType -> Mark -> Mark -> UEnvLow -> UEnvMid 
  --     UEnvAp1 : UEnvLow -> Mark -> ExpLow -> UEnvMid 
  --     UEnvAp2 : ExpLow -> Mark -> UEnvLow -> UEnvMid 
  --     UEnvAsc : NewType -> UEnvLow -> UEnvMid 

  --   data UEnvLow : Set where 
  --     UEnvLowRec : UEnvUp -> Mark -> NewData -> UEnvLow 

  mutual 
    -- data _L⟦_⟧U≡_ : (ε : LEnvUp) (e : ExpLow) (e' : ExpUp)  -> Set where
    --   FillLEnvUpRec : ∀ {e ε e' syn} ->
    --     ε L⟦ e ⟧M≡ e' ->
    --     (LEnvUpRec ε syn) L⟦ e ⟧U≡ (e' ⇒ syn)

    data _L⟦_⟧M≡_ : (ε : LEnvMid) (e : ExpLow) (e' : ExpMid)  -> Set where
      FillLEnvFun : ∀ {e ε e' x t m1 m2} ->
        ε L⟦ e ⟧L≡ e' ->
        (LEnvFun x t m1 m2 ε) L⟦ e ⟧M≡ (EFun x t m1 m2 e')
      FillLEnvAp1 : ∀ {e ε e' e2 m} ->
        ε L⟦ e ⟧L≡ e' ->
        (LEnvAp1 ε m e2) L⟦ e ⟧M≡ (EAp e' m e2)
      FillLEnvAp2 : ∀ {e ε e' e1 m} ->
        ε L⟦ e ⟧L≡ e' ->
        (LEnvAp2 e1 m ε) L⟦ e ⟧M≡ (EAp e1 m e')
      FillLEnvAsc : ∀ {e ε e' t} ->
        ε L⟦ e ⟧L≡ e' ->
        (LEnvAsc t ε) L⟦ e ⟧M≡ (EAsc t e')

    data _L⟦_⟧L≡_ : (ε : LEnvLow) (e : ExpLow) (e' : ExpLow)  -> Set where
      FillL⊙ : ∀ {e} ->
        L⊙ L⟦ e ⟧L≡ e
      FillLEnvLowRec : ∀ {e e' ana syn m ε} ->
        ε L⟦ e ⟧M≡ e' ->
        LEnvLowRec ana ε syn m L⟦ e ⟧L≡ (ana ⇒ e' ⇒ syn [ m ])

  -- mutual 
  --   data _U⟦_⟧U≡_ : (ε : UEnvUp) (e : ExpUp) (e' : ExpUp)  -> Set where
  --     FillU⊙ : ∀ {e} ->
  --       U⊙ U⟦ e ⟧U≡ e
  --     FillUEnvUpRec : ∀ {e ε e' syn} ->
  --       ε U⟦ e ⟧M≡ e' ->
  --       (UEnvUpRec ε syn) U⟦ e ⟧U≡ (e' ⇒ syn)

  --   data _U⟦_⟧M≡_ : (ε : UEnvMid) (e : ExpUp) (e' : ExpMid)  -> Set where
  --     FillUEnvFun : ∀ {e ε e' x t m1 m2} ->
  --       ε U⟦ e ⟧L≡ e' ->
  --       (UEnvFun x t m1 m2 ε) U⟦ e ⟧M≡ (EFun x t m1 m2 e')
  --     FillUEnvAp1 : ∀ {e ε e' e2 m} ->
  --       ε U⟦ e ⟧L≡ e' ->
  --       (UEnvAp1 ε m e2) U⟦ e ⟧M≡ (EAp e' m e2)
  --     FillUEnvAp2 : ∀ {e ε e' e1 m} ->
  --       ε U⟦ e ⟧L≡ e' ->
  --       (UEnvAp2 e1 m ε) U⟦ e ⟧M≡ (EAp e1 m e')
  --     FillUEnvAsc : ∀ {e ε e' t} ->
  --       ε U⟦ e ⟧L≡ e' ->
  --       (UEnvAsc t ε) U⟦ e ⟧M≡ (EAsc t e')

  --   data _U⟦_⟧L≡_ : (ε : UEnvLow) (e : ExpUp) (e' : ExpLow)  -> Set where
  --     FillUEnvLowRec : ∀ {e e' ana m ε} ->
  --       ε U⟦ e ⟧U≡ e' ->
  --       UEnvLowRec ε m ana U⟦ e ⟧L≡ (e' [ m ]⇐ ana)

  -- mutual 

  --   ComposeULU : UEnvLow -> LEnvUp -> UEnvUp
  --   ComposeULU ε1 (LEnvUpRec ε2 t) = UEnvUpRec (ComposeULM ε1 ε2) t
    
  --   ComposeULM : UEnvLow -> LEnvMid -> UEnvMid
  --   ComposeULM ε1 (LEnvFun x t m1 m2 ε2) = UEnvFun x t m1 m2 (ComposeULL ε1 ε2)
  --   ComposeULM ε1 (LEnvAp1 ε2 m e2) = UEnvAp1 (ComposeULL ε1 ε2) m e2
  --   ComposeULM ε1 (LEnvAp2 e1 m ε2) = UEnvAp2 e1 m (ComposeULL ε1 ε2)
  --   ComposeULM ε1 (LEnvAsc t ε2) = UEnvAsc t (ComposeULL ε1 ε2)

  --   ComposeULL : UEnvLow -> LEnvLow -> UEnvLow 
  --   ComposeULL ε1 L⊙ = ε1
  --   ComposeULL ε1 (LEnvLowRec ε2 m ana) = UEnvLowRec (ComposeULU ε1 ε2) m ana
  
  -- mutual 

  --   ComposeLLU : LEnvLow -> LEnvUp -> LEnvUp
  --   ComposeLLU ε1 (LEnvUpRec ε2 t) = LEnvUpRec (ComposeLLM ε1 ε2) t
    
  --   ComposeLLM : LEnvLow -> LEnvMid -> LEnvMid
  --   ComposeLLM ε1 (LEnvFun x t m1 m2 ε2) = LEnvFun x t m1 m2 (ComposeLLL ε1 ε2)
  --   ComposeLLM ε1 (LEnvAp1 ε2 m e2) = LEnvAp1 (ComposeLLL ε1 ε2) m e2
  --   ComposeLLM ε1 (LEnvAp2 e1 m ε2) = LEnvAp2 e1 m (ComposeLLL ε1 ε2)
  --   ComposeLLM ε1 (LEnvAsc t ε2) = LEnvAsc t (ComposeLLL ε1 ε2)

  --   ComposeLLL : LEnvLow -> LEnvLow -> LEnvLow 
  --   ComposeLLL ε1 L⊙ = ε1
  --   ComposeLLL ε1 (LEnvLowRec ε2 m ana) = LEnvLowRec (ComposeLLU ε1 ε2) m ana
  
  -- mutual 

  --   ComposeUUU : UEnvUp -> UEnvUp -> UEnvUp
  --   ComposeUUU ε1 U⊙ = ε1
  --   ComposeUUU ε1 (UEnvUpRec ε2 t) = UEnvUpRec (ComposeUUM ε1 ε2) t
    
  --   ComposeUUM : UEnvUp -> UEnvMid -> UEnvMid
  --   ComposeUUM ε1 (UEnvFun x t m1 m2 ε2) = UEnvFun x t m1 m2 (ComposeUUL ε1 ε2)
  --   ComposeUUM ε1 (UEnvAp1 ε2 m e2) = UEnvAp1 (ComposeUUL ε1 ε2) m e2
  --   ComposeUUM ε1 (UEnvAp2 e1 m ε2) = UEnvAp2 e1 m (ComposeUUL ε1 ε2)
  --   ComposeUUM ε1 (UEnvAsc t ε2) = UEnvAsc t (ComposeUUL ε1 ε2)

  --   ComposeUUL : UEnvUp -> UEnvLow -> UEnvLow 
  --   ComposeUUL ε1 (UEnvLowRec ε2 m ana) = UEnvLowRec (ComposeUUU ε1 ε2) m ana
  
  -- mutual 

  --   ComposeLUU : LEnvUp -> UEnvUp -> LEnvUp
  --   ComposeLUU ε1 U⊙ = ε1
  --   ComposeLUU ε1 (UEnvUpRec ε2 t) = LEnvUpRec (ComposeLUM ε1 ε2) t
    
  --   ComposeLUM : LEnvUp -> UEnvMid -> LEnvMid
  --   ComposeLUM ε1 (UEnvFun x t m1 m2 ε2) = LEnvFun x t m1 m2 (ComposeLUL ε1 ε2)
  --   ComposeLUM ε1 (UEnvAp1 ε2 m e2) = LEnvAp1 (ComposeLUL ε1 ε2) m e2
  --   ComposeLUM ε1 (UEnvAp2 e1 m ε2) = LEnvAp2 e1 m (ComposeLUL ε1 ε2)
  --   ComposeLUM ε1 (UEnvAsc t ε2) = LEnvAsc t (ComposeLUL ε1 ε2)

  --   ComposeLUL : LEnvUp -> UEnvLow -> LEnvLow 
  --   ComposeLUL ε1 (UEnvLowRec ε2 m ana) = LEnvLowRec (ComposeLUU ε1 ε2) m ana

  -- mutual 

  --   FillULU : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 U⟦ e1 ⟧L≡ e2 -> 
  --     ε2 L⟦ e2 ⟧U≡ e3 ->
  --     (ComposeULU ε1 ε2) U⟦ e1 ⟧U≡ e3
  --   FillULU fill1 (FillLEnvUpRec fill2) = FillUEnvUpRec (FillULM fill1 fill2)

  --   FillULM : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 U⟦ e1 ⟧L≡ e2 -> 
  --     ε2 L⟦ e2 ⟧M≡ e3 ->
  --     (ComposeULM ε1 ε2) U⟦ e1 ⟧M≡ e3
  --   FillULM fill1 (FillLEnvFun fill2) = FillUEnvFun (FillULL fill1 fill2)
  --   FillULM fill1 (FillLEnvAp1 fill2) = FillUEnvAp1 (FillULL fill1 fill2)
  --   FillULM fill1 (FillLEnvAp2 fill2) = FillUEnvAp2 (FillULL fill1 fill2)
  --   FillULM fill1 (FillLEnvAsc fill2) = FillUEnvAsc (FillULL fill1 fill2)

  --   FillULL : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 U⟦ e1 ⟧L≡ e2 -> 
  --     ε2 L⟦ e2 ⟧L≡ e3 -> 
  --     (ComposeULL ε1 ε2) U⟦ e1 ⟧L≡ e3
  --   FillULL fill1 FillL⊙ = fill1 
  --   FillULL fill1 (FillLEnvLowRec fill2) = FillUEnvLowRec (FillULU fill1 fill2)
  
  -- mutual 

  --   FillLLU : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 L⟦ e1 ⟧L≡ e2 -> 
  --     ε2 L⟦ e2 ⟧U≡ e3 ->
  --     (ComposeLLU ε1 ε2) L⟦ e1 ⟧U≡ e3
  --   FillLLU fill1 (FillLEnvUpRec fill2) = FillLEnvUpRec (FillLLM fill1 fill2)

  --   FillLLM : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 L⟦ e1 ⟧L≡ e2 -> 
  --     ε2 L⟦ e2 ⟧M≡ e3 ->
  --     (ComposeLLM ε1 ε2) L⟦ e1 ⟧M≡ e3
  --   FillLLM fill1 (FillLEnvFun fill2) = FillLEnvFun (FillLLL fill1 fill2)
  --   FillLLM fill1 (FillLEnvAp1 fill2) = FillLEnvAp1 (FillLLL fill1 fill2)
  --   FillLLM fill1 (FillLEnvAp2 fill2) = FillLEnvAp2 (FillLLL fill1 fill2)
  --   FillLLM fill1 (FillLEnvAsc fill2) = FillLEnvAsc (FillLLL fill1 fill2)

  --   FillLLL : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 L⟦ e1 ⟧L≡ e2 -> 
  --     ε2 L⟦ e2 ⟧L≡ e3 -> 
  --     (ComposeLLL ε1 ε2) L⟦ e1 ⟧L≡ e3
  --   FillLLL fill1 FillL⊙ = fill1 
  --   FillLLL fill1 (FillLEnvLowRec fill2) = FillLEnvLowRec (FillLLU fill1 fill2)

  -- mutual 

  --   FillUUU : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 U⟦ e1 ⟧U≡ e2 -> 
  --     ε2 U⟦ e2 ⟧U≡ e3 ->
  --     (ComposeUUU ε1 ε2) U⟦ e1 ⟧U≡ e3
  --   FillUUU fill1 FillU⊙ = fill1 
  --   FillUUU fill1 (FillUEnvUpRec fill2) = FillUEnvUpRec (FillUUM fill1 fill2)

  --   FillUUM : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 U⟦ e1 ⟧U≡ e2 -> 
  --     ε2 U⟦ e2 ⟧M≡ e3 ->
  --     (ComposeUUM ε1 ε2) U⟦ e1 ⟧M≡ e3
  --   FillUUM fill1 (FillUEnvFun fill2) = FillUEnvFun (FillUUL fill1 fill2)
  --   FillUUM fill1 (FillUEnvAp1 fill2) = FillUEnvAp1 (FillUUL fill1 fill2)
  --   FillUUM fill1 (FillUEnvAp2 fill2) = FillUEnvAp2 (FillUUL fill1 fill2)
  --   FillUUM fill1 (FillUEnvAsc fill2) = FillUEnvAsc (FillUUL fill1 fill2)

  --   FillUUL : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 U⟦ e1 ⟧U≡ e2 -> 
  --     ε2 U⟦ e2 ⟧L≡ e3 -> 
  --     (ComposeUUL ε1 ε2) U⟦ e1 ⟧L≡ e3
  --   FillUUL fill1 (FillUEnvLowRec fill2) = FillUEnvLowRec (FillUUU fill1 fill2)

  -- mutual 

  --   FillLUU : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 L⟦ e1 ⟧U≡ e2 -> 
  --     ε2 U⟦ e2 ⟧U≡ e3 ->
  --     (ComposeLUU ε1 ε2) L⟦ e1 ⟧U≡ e3
  --   FillLUU fill1 FillU⊙ = fill1 
  --   FillLUU fill1 (FillUEnvUpRec fill2) = FillLEnvUpRec (FillLUM fill1 fill2)

  --   FillLUM : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 L⟦ e1 ⟧U≡ e2 -> 
  --     ε2 U⟦ e2 ⟧M≡ e3 ->
  --     (ComposeLUM ε1 ε2) L⟦ e1 ⟧M≡ e3
  --   FillLUM fill1 (FillUEnvFun fill2) = FillLEnvFun (FillLUL fill1 fill2)
  --   FillLUM fill1 (FillUEnvAp1 fill2) = FillLEnvAp1 (FillLUL fill1 fill2)
  --   FillLUM fill1 (FillUEnvAp2 fill2) = FillLEnvAp2 (FillLUL fill1 fill2)
  --   FillLUM fill1 (FillUEnvAsc fill2) = FillLEnvAsc (FillLUL fill1 fill2)

  --   FillLUL : ∀ {ε1 ε2 e1 e2 e3} ->
  --     ε1 L⟦ e1 ⟧U≡ e2 -> 
  --     ε2 U⟦ e2 ⟧L≡ e3 -> 
  --     (ComposeLUL ε1 ε2) L⟦ e1 ⟧L≡ e3
  --   FillLUL fill1 (FillUEnvLowRec fill2) = FillLEnvLowRec (FillLUU fill1 fill2)