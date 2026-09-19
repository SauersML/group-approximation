---
rg: 2
id: fix-nm-full-gl01-triangle
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL01.Triangle: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/GL01/Triangle.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL01/Triangle.lean:78:71: unsolved goals
error: GroupApproximation/Manuscript/NonMF/Full/GL01/Triangle.lean:78:80: This simp argument is unused:
error: GroupApproximation/Manuscript/NonMF/Full/GL01/Triangle.lean:341:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.false_of_triangle_walk' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/NonMF/Full/GL01/Triangle.lean:342:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.GL01.false_of_corner' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL01.Triangle` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
