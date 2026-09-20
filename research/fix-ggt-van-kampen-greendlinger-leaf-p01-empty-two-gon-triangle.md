---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p01-empty-two-gon-triangle
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.TriangleCorner: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01EmptyTwoGon/TriangleCorner.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01EmptyTwoGon/TriangleCorner.lean:86:71: unsolved goals
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01EmptyTwoGon/TriangleCorner.lean:86:80: This simp argument is unused:
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01EmptyTwoGon/TriangleCorner.lean:268:6: 'simpa only [dartWord, RelLetter.listVal, List.map_cons, List.prod_cons] using h0' tactic does nothing
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01EmptyTwoGon/TriangleCorner.lean:330:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.exists_section_of_lt' depends on axioms outside the classical allowlist: [
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.TriangleCorner` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
