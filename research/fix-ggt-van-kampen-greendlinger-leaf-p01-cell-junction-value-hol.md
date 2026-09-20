---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p01-cell-junction-value-hol
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Hole: Function expected at"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01CellJunctionValue/Hole.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01CellJunctionValue/Hole.lean:211:59: Function expected at
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01CellJunctionValue/Hole.lean:233:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.exists_holeRegion' depends on axioms outside the classical allowlist: [s
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Hole` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
