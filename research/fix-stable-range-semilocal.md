---
rg: 2
id: fix-stable-range-semilocal
kind: claim
title: "Fix GroupApproximation.StableRange.Semilocal: Unknown identifier on"
---

**OPEN.** Lean module `GroupApproximation/StableRange/Semilocal.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: fix-bh-a.

**First errors (verbatim).**

```
error: GroupApproximation/StableRange/Semilocal.lean:32:35: Unknown identifier `on`
error: GroupApproximation/StableRange/Semilocal.lean:28:33: unsolved goals
error: GroupApproximation/StableRange/Semilocal.lean:70:14: 'GroupApproximation.StableRange.stableRangeLE_one_of_finite_maximal' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/StableRange/Semilocal.lean:78:14: 'GroupApproximation.StableRange.stableRangeLE_one_of_isLocalRing' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.StableRange.Semilocal` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
