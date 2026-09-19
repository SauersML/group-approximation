---
rg: 2
id: fix-nm-full-gl06b-outer-side-transport
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL06b.OuterSideTransport: Variable name y is not explicitly referenced."
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/GL06b/OuterSideTransport.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL06b/OuterSideTransport.lean:147:29: Variable name `y` is not explicitly referenced.
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL06b.OuterSideTransport` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
