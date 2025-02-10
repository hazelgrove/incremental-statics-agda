module Core where 
  
  import Core.Core
  import Core.Environment

  import Core.Marking
  import Core.WellTyped
  import Core.Settled
  
  import Core.Validity
  
  import Core.VarsSynthesize
  import Core.Lemmas-Preservation

  import Core.Update
  import Core.UpdatePreservation

  import Core.Actions
  import Core.ActionPreservation

  import Core.Progress
  import Core.SettledDec
  import Core.Termination

  import Core.MarkingUnicity
  import Core.ActionUnicity
  import Core.ActionErasure
  import Core.UpdateErasure

  import Core.Main