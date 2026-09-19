---
rg: 2
id: fix-bhmet-absorption-suslin-euclid-kill
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidKill: Type mismatch"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**RESOLVED (d2df12ed90).** Lean module `GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinEuclidKill.lean` failed to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 2 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: yes.

**Repair landed, unprobed.** d2df12ed90: BH metabelian chain: repair 27 red modules (unprobed) and rewire FrontierFour to route A. It was OPEN until a trusted probe built it green; see below.

**Green.** Built green (lake ✔ or replay) by the trusted gqprobe-lean v4 batch, Slurm job 1328760 (request 2, log gq-slurm/batch-b1789769423-2.log, lane bh-pal-wire; that request completed, red only in the three modules still open). This module compiled with no errors and clean `#audit_axioms`. The compiled bytes are main's d2df12ed90 bytes: 567 of the 572 `#audit_axioms` positions in that log match main's files, and the 5 misses are all in the two files that 55aba370a4 re-repaired afterwards. The job was cancelled later, during request 3. Since then no file in this module's import closure has changed on main, only downstream modules and a lakefile comment. That cancellation is why the index loop, which requires a completed batch, did not record it.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinEuclidKill.lean:108:12: Type mismatch
error: GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinEuclidKill.lean:109:12: Type mismatch
```

**Kind.** proof error (classification merged from the parallel node `fix-bh-met-absorption-suslin-euclid-kill`, now superseded).

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidKill` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
