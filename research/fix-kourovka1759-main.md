---
rg: 2
id: fix-kourovka1759-main
kind: claim
title: "Fix GroupApproximation.Kourovka1759.Main: Unknown constant Equiv.Perm.apply_inv_self"
---

**RESOLVED (1f7bd2d0fe, trusted batched probe job 1290512).** Previously OPEN. Lean module `GroupApproximation/Kourovka1759/Main.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-kourovka59.


**First errors (verbatim).**

```
error: GroupApproximation/Kourovka1759/Main.lean:107:9: Unknown constant `Equiv.Perm.apply_inv_self`
error: GroupApproximation/Kourovka1759/Main.lean:104:49: unsolved goals
```

**What it needs.** Make `GroupApproximation.Kourovka1759.Main` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
