---
rg: 2
id: fix-nm-full-torsion-free-endpoints-reductions
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.TorsionFreeEndpoints.Reductions: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/TorsionFreeEndpoints/Reductions.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.TorsionFreeEndpoints.Reductions` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
