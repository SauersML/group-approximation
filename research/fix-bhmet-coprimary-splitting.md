---
rg: 2
id: fix-bhmet-coprimary-splitting
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.CoprimarySplitting: failed to compile definition, consider marking it as 'noncomputable'"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CoprimarySplitting.lean` failed to build in the trusted gqprobe-lean v4 batch, Slurm job 1328760 (09-18, base d2df12ed9 plus bh-pal-wire's wave-1 overlay; request log gq-slurm/batch-b1789769423-3.log; 1 error lines, including the axiom-guard lines that follow them). Its imports built green in that batch, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire. Node written by fix-bh-b.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CoprimarySplitting.lean:37:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'MonoidAlgebra.semiring', which is 'noncomputable'
```

**Kind.** mechanical: a definition depends on the noncomputable `MonoidAlgebra.semiring`.

**Repair landed, unprobed.** 55aba370a4 (bh-pal-wire) wraps the namespace body in `noncomputable section` … `end`. fix-bh-b reviewed it statically (09-19) and found nothing further.

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CoprimarySplitting` compile with the repository's `-DwarningAsError=true` settings, changing no statement. Slurm submission has been blocked since 09-18 ~20:55 (state/SLURM-BLOCKED), so no trusted build has run since the repair landed.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
