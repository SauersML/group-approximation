---
rg: 2
id: fix-nm-full-gl02-window-shape-head-shape-deps
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.HeadShapeDeps: Variable name Q is not explicitly referenced."
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/GL02/WindowShape/HeadShapeDeps.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**Repair landed, unprobed.** c7f48edeb7: NM GL01/Triangle, GL02/WindowShape/HeadShapeDeps: root-closure reds fixed (GREEN). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL02/WindowShape/HeadShapeDeps.lean:76:41: Variable name `Q` is not explicitly referenced.
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.HeadShapeDeps` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
