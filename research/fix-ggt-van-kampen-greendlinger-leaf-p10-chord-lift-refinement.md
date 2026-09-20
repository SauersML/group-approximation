---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p10-chord-lift-refinement
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Refinement: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10ChordLift/Refinement.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10ChordLift/Refinement.lean:243:4: unsolved goals
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10ChordLift/Refinement.lean:275:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.edgeInsertion' depends on axioms outside the classical allowlis
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Refinement` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
