---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p01-section-corners-corners
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.Corners: Tactic rewrite failed: motive is not type correct:"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01SectionCorners/Corners.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01SectionCorners/Corners.lean:62:26: Tactic `rewrite` failed: motive is not type correct:
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01SectionCorners/Corners.lean:244:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.outerArc_getElem?' depends on axioms outside the classical allowlist: [sorr
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01SectionCorners/Corners.lean:245:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.boundary_ends' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01SectionCorners/Corners.lean:247:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.exists_cornerAt' depends on axioms outside the classical allowlist: [sorryA
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01SectionCorners.Corners` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
