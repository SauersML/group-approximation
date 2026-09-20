---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p05-region-pair-rotation
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.Rotation: Variable name x is not explicitly referenced."
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05RegionPair/Rotation.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05RegionPair/Rotation.lean:66:7: Variable name `x` is not explicitly referenced.
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05RegionPair/Rotation.lean:66:9: Variable name `y` is not explicitly referenced.
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.Rotation` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
