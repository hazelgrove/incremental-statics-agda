
module Core where 
  
  import Core.Core
  import Core.Environment

  import Core.Marking
  import Core.WellTyped
  
  import Core.Settled
  import Core.Validity
  
  import Core.Lemmas
  
  import Core.VarsSynthesize
  import Core.Update
  import Core.Actions

  import Core.VarsSynthesizePreservation
  import Core.UpdatePreservation
  import Core.ActionPreservation

  import Core.MarkingUnicity
  import Core.ActionUnicity

  import Core.VarsSynthesizeErasure
  import Core.UpdateErasure
  import Core.ActionErasure

  import Core.Progress
  import Core.Termination

  import Core.Main 