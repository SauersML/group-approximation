---
rg: 2
id: fix-bhmet-char-p-host-tree-group
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeGroup: automatically included section variable(s) unused"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeGroup.lean` failed to build in the trusted gqprobe-lean v4 batch, Slurm job 1328760 (09-18, base d2df12ed9 plus bh-pal-wire's wave-1 overlay; request log gq-slurm/batch-b1789769423-3.log; 4 error lines, including the axiom-guard lines that follow them). Its imports built green in that batch, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire. Node written by fix-bh-b.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeGroup.lean:47:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affMat_mul`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeGroup.lean:53:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affVec_mul`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeGroup.lean:59:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affMat_one`:
error: GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeGroup.lean:64:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.affVec_one`:
```

**Kind.** mechanical (Lean/Mathlib drift): the unused-section-variable linter fires on 4 theorems.

**Repair landed, unprobed.** 55aba370a4 (bh-pal-wire) adds `omit [DecidableEq σ] in` to affMat_mul, affVec_mul, affMat_one and affVec_one, which is exactly the variable set the linter named. fix-bh-b reviewed it statically (09-19) and found nothing further.

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeGroup` compile with the repository's `-DwarningAsError=true` settings, changing no statement. Slurm submission has been blocked since 09-18 ~20:55 (state/SLURM-BLOCKED), so no trusted build has run since the repair landed.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
