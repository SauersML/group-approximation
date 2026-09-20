---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-piece04-window-shape-window
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplitAux: List.getLast?_eq_getLast has been deprecated: Use List.getLast?_eq_som"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/WindowShape/WindowHeadSplitAux.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789919140 on main 57f90fce37).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/WindowShape/WindowHeadSplitAux.lean:114:12: `List.getLast?_eq_getLast` has been deprecated: Use `List.getLast?_eq_some_getLast` instead
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/WindowShape/WindowHeadSplitAux.lean:116:56: `List.getLast?_eq_getLast` has been deprecated: Use `List.getLast?_eq_some_getLast` instead
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplitAux` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
