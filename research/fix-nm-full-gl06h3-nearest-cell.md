---
rg: 2
id: fix-nm-full-gl06h3-nearest-cell
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL06h3.NearestCell: Used tac1 <;> tac2 where (tac1; tac2) would suffice"
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMF/Full/GL06h3/NearestCell.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.


**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL06h3/NearestCell.lean:246:13: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL06h3.NearestCell` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
