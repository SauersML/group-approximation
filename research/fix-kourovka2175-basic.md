---
rg: 2
id: fix-kourovka2175-basic
kind: claim
title: "Fix GroupApproximation.Kourovka2175.Basic: Unknown constant Equiv.Perm.apply_inv_self"
---

**RESOLVED (1f7bd2d0fe, trusted batched probe job 1290512).** Previously OPEN. Lean module `GroupApproximation/Kourovka2175/Basic.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-integrate.


**First errors (verbatim).**

```
error: GroupApproximation/Kourovka2175/Basic.lean:103:6: Unknown constant `Equiv.Perm.apply_inv_self`
error: GroupApproximation/Kourovka2175/Basic.lean:167:42: This simp argument is unused:
```

**What it needs.** Make `GroupApproximation.Kourovka2175.Basic` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
