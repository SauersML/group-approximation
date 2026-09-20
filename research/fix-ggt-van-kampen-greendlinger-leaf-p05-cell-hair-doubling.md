---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p05-cell-hair-doubling
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Doubling: Type mismatch"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellHair/Doubling.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellHair/Doubling.lean:79:6: Type mismatch
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellHair/Doubling.lean:88:8: Type mismatch
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellHair/Doubling.lean:205:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.faceOf_embed_mem_faceSet' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellHair/Doubling.lean:206:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.regionInternal_embed_iff' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Doubling` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
