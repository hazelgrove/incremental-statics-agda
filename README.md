# Incremental MALC Mechanization

This repository contains the full Agda mechanization of the incremental marked and annotated lamnda calculus (Incremental MALC) as defined in the paper "Incremental Bidirectional Typing via Order Maintenance." To check the proofs, an installation of [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download) is required. The proofs are known to load cleanly under Agda `2.6.4`.

Once, installed `agda All.agda` in the top-level directory will cause Agda to check all the proofs.

## Where to Find Each Theorem

Here is where to find each definition:

<!-- - [Core/Core.agda](./Core/Core.agda) contains the syntax of Incremental MALC, as well as generic judgments like subsumable forms and context lookup.  -->

- [Core/Main](./Core/Main.agda) contains the three main theorems of correctness for Incremental MALC:
  - Validity
  - Convergence
  - Termination

- [Core/ActionCompleteness](./Core/ActionCompleteness.agda) contains the proof of the Action Completeness theorem, validating the expressiveness of our chosen set of actions.

The other included proofs support these four theorems. The name of the file corresponds to the name of the lemma in the publication.  
