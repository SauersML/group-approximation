---
rg: 2
id: fix-nm-full-gl06f-reduction
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL06f.Reduction: failed to synthesize instance of type class"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMF/Full/GL06f/Reduction.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL06f/Reduction.lean:56:6: failed to synthesize instance of type class
error: GroupApproximation/Manuscript/NonMF/Full/GL06f/Reduction.lean:104:8: Type mismatch
error: GroupApproximation/Manuscript/NonMF/Full/GL06f/Reduction.lean:294:14: 'GroupApproximation.Full.GL06f.isBoundaryDart_flipFaces_iff' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/NonMF/Full/GL06f/Reduction.lean:300:14: 'GroupApproximation.Full.GL06f.rose_of_regionMoveSubArc' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL06f.Reduction` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
