---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-piece04-window-shape-head-s
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.HeadShapeDeps: Variable name Q is not explicitly referenced."
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/WindowShape/HeadShapeDeps.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/WindowShape/HeadShapeDeps.lean:71:41: Variable name `Q` is not explicitly referenced.
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.HeadShapeDeps` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
