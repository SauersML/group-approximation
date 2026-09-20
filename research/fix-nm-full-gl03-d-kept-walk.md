---
rg: 2
id: fix-nm-full-gl03-d-kept-walk
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL03D.KeptWalk: Insufficient number of fields for ⟨...⟩ constructor: Constructor Iff.i"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/GL03D/KeptWalk.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It IS in the root closure: the root build is red until it is fixed (top priority).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789919140 on main 57f90fce37).**

```
error: GroupApproximation/Manuscript/NonMF/Full/GL03D/KeptWalk.lean:55:10: Insufficient number of fields for `⟨...⟩` constructor: Constructor `Iff.intro` has 2 explicit field, but only 1 was provided
error: GroupApproximation/Manuscript/NonMF/Full/GL03D/KeptWalk.lean:354:14: 'GroupApproximation.Full.GL03D.sideColour_step' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/NonMF/Full/GL03D/KeptWalk.lean:355:14: 'GroupApproximation.Full.GL03D.flipFaces_sideColour' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/NonMF/Full/GL03D/KeptWalk.lean:357:14: 'GroupApproximation.Full.GL03D.regionMove_of_keptWalk' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL03D.KeptWalk` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
