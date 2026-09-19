---
rg: 2
id: fix-nm-full-gl06d-outer-monogon-diagram
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL06d.OuterMonogonDiagram: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/GL06d/OuterMonogonDiagram.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL06d/OuterMonogonDiagram.lean:117:2: unsolved goals
error: GroupApproximation/Manuscript/NonMF/Full/GL06d/OuterMonogonDiagram.lean:221:48: Unknown identifier `RelWord.revInv`
error: GroupApproximation/Manuscript/NonMF/Full/GL06d/OuterMonogonDiagram.lean:228:11: Unknown identifier `RelWord.revInv`
error: GroupApproximation/Manuscript/NonMF/Full/GL06d/OuterMonogonDiagram.lean:289:14: 'GroupApproximation.Full.GL06d.sameCorner_mid' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL06d.OuterMonogonDiagram` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
