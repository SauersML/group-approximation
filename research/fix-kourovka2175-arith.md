---
rg: 2
id: fix-kourovka2175-arith
kind: claim
title: "Fix GroupApproximation.Kourovka2175.Arith: unsolved goals"
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/Kourovka2175/Arith.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: fix-bh-b.


**First errors (verbatim).**

```
error: GroupApproximation/Kourovka2175/Arith.lean:130:21: unsolved goals
error: GroupApproximation/Kourovka2175/Arith.lean:130:21: unsolved goals
error: GroupApproximation/Kourovka2175/Arith.lean:130:21: unsolved goals
error: GroupApproximation/Kourovka2175/Arith.lean:130:21: unsolved goals
```

**What it needs.** Make `GroupApproximation.Kourovka2175.Arith` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
