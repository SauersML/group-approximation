---
rg: 2
id: fix-bhmet-elem-fpk2-local-quillen-ideal
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenIdeal: Application type mismatch: The argument"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**RESOLVED (d2df12ed90).** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPK2LocalQuillenIdeal.lean` failed to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 1 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** d2df12ed90: BH metabelian chain: repair 27 red modules (unprobed) and rewire FrontierFour to route A. It was OPEN until a trusted probe built it green; see below.

**Green.** Built green by the trusted gqprobe-lean v4 batch, Slurm job 1328760 (request 2, log gq-slurm/batch-b1789769423-2.log, lane bh-pal-wire; that request completed and was red only in AffineFPModel, PureCharPrimeEHighWittECoeff and PureCharPrimeEHighArtinHasseAlg). This module compiled with no errors, so every `#audit_axioms` guard passed. The compiled bytes are main's d2df12ed90 bytes: every `#audit_axioms` position in that log for this file matches main's file. None of the 112 files in its GroupApproximation import closure changed on main between the batch's snapshot (main at 17:10-17:25 CDT, 09-18) and 09-19 (checked by fix-bh-b). The job was cancelled later, during request 3, and the index loop does not read verdicts from a cancelled batch, which is why it did not record this one. (This corrects an earlier citation of 2d6ebaf55, which is not a commit on main. The same correction for the other resolved nodes is fix-bh-a's 26ff7727f8.)

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2LocalQuillenIdeal.lean:120:63: Application type mismatch: The argument
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-elem-fpk2-local-quillen-ideal`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenIdeal` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
