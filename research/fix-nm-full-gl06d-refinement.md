---
rg: 2
id: fix-nm-full-gl06d-refinement
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL06d.Refinement: unsolved goals"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMF/Full/GL06d/Refinement.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL06d/Refinement.lean:223:4: unsolved goals
error: GroupApproximation/Manuscript/NonMF/Full/GL06d/Refinement.lean:252:14: 'GroupApproximation.Full.GL06d.RotationRefinement.edgeInsertion' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL06d.Refinement` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
