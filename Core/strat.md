Theorems:
- Main Theorem
  - Incremental Correctness
    - Action preservation
    - Update preservation
    - Progress
    - Incremental Validity
  - Enriched Action Correspondence
  - Grove Action Commutativity
    - Grove Action Correspondence
    - Graph Action Commutativity
    - Recomposability
- Termination

--------------------------------------------------------------------------------

Preservation: actions and update steps preserve well-typedness
Progress: each well-typed program either can step or is settled 
Correctness: each well-typed, settled program agrees with from-scratch marking 
Termination: a program cannot update step forever 

--------------------------------------------------------------------------------

Main theorem: 

Prelims:
- P* is enriched grove/program (with info)
- done := cannot take an update step
- stuff := sequence of actions & updates
- stuff1 ~ stuff2 := they have the same set of actions
- stuff(P) := apply actions in order and updates whenever you want, until you can't

Statement: 
- If: stuff1 ~ stuff2
- And: well-typed(P*)
- Then: stuff1(P*) = stuff2(P*) = mark(P'), where P' = bare(stuff1)(bare(P*)) = bare(stuff1)(bare(P*))

Proof:
  stuff1(P*) 
  = mark(bare(stuff1(P*))) (KEY1 : incremental correctness)
  = mark(bare(stuff1)(bare(P*))) (KEY2 : enriched action correspondence)
  = mark(bare(stuff2)(bare(P*))) (KEY3 : action commutativity)
  = mark(bare(stuff2(P*))) (KEY2)
  = stuff2(P*) (KEY1)

KEY1 (incremental correctness):
- If: well-typed(P*)
- Then: stuff(P*) = mark(bare(stuff(P*)))

Proof: 
- well-typed(stuff(P*)) (by action and update preservation)
- done(stuff(P*)) (by definition of stuff application)
- settled(stuff(P*)) (by progress: "done implies settled")
- stuff(P*) = mark(bare(stuff(P*))) (incremental validity on settled & well-typed programs)

KEY2 (enriched action correspondence): 
- bare(a(P*)) = bare(a)(bare(P*))

Proof:
- Should be trivial, direct induction

KEY3 (action commutativity):

Prelims:
- d = decomp, r = recomp

Statement:
- a1(a2(P)) = a2(a1(P))

Proof:
a1(a2(P)) 
= d(patch(a1)(r(d(patch(a2)(r(P)))))) (by grove action correspondence)
= d(patch(a1)(patch(a2)(r(P)))) (by decomp-recomp)
= d(patch(a2)(patch(a1)(r(P)))) (by patch commutativity)
= d(patch(a2)(r(d(patch(a1)(r(P)))))) (by decomp-recomp)
= a2(a1(P)) 
