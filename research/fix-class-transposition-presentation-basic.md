---
rg: 2
id: fix-class-transposition-presentation-basic
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Presentation.Basic: Unknown constant Equiv.Perm.apply_inv_self"
---

**OPEN.** Lean module `GroupApproximation/ClassTransposition/Presentation/Basic.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-kourovka61.

**First errors (verbatim).**

```
error: GroupApproximation/ClassTransposition/Presentation/Basic.lean:53:60: Unknown constant `Equiv.Perm.apply_inv_self`
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Presentation.Basic` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
