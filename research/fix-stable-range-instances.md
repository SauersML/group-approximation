---
rg: 2
id: fix-stable-range-instances
kind: claim
title: "Fix GroupApproximation.StableRange.Instances: Type mismatch"
---

**OPEN.** Lean module `GroupApproximation/StableRange/Instances.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: fix-bh-a.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/StableRange/Instances.lean:53:2: Type mismatch
error: GroupApproximation/StableRange/Instances.lean:55:14: 'GroupApproximation.StableRange.stableRangeLE_mvPolynomial_of_isNoetherianRing' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/StableRange/Instances.lean:87:14: 'GroupApproximation.StableRange.stableRangeLE_mvPolynomial_away' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.StableRange.Instances` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
