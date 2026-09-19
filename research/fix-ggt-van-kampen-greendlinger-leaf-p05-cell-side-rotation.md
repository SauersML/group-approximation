---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p05-cell-side-rotation
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Rotation: Variable name x is not explicitly referenced."
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellSide/Rotation.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellSide/Rotation.lean:62:7: Variable name `x` is not explicitly referenced.
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05CellSide/Rotation.lean:62:9: Variable name `y` is not explicitly referenced.
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Rotation` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
