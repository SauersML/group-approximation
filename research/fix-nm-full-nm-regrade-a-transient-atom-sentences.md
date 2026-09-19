---
rg: 2
id: fix-nm-full-nm-regrade-a-transient-atom-sentences
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.NMRegradeA.TransientAtomSentences: Set.diff_eq has been deprecated: Use Set.sdiff_eq instead"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/Manuscript/NonMF/Full/NMRegradeA/TransientAtomSentences.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-nm-partial-a.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/NonMF/Full/NMRegradeA/TransientAtomSentences.lean:115:12: `Set.diff_eq` has been deprecated: Use `Set.sdiff_eq` instead
```

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.NMRegradeA.TransientAtomSentences` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
