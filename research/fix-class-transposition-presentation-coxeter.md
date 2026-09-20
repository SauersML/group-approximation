---
rg: 2
id: fix-class-transposition-presentation-coxeter
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Presentation.Coxeter: Unknown constant Equiv.Perm.apply_inv_self"
---

**RESOLVED (4067aaa686, trusted batched probe job direct-b1789912910).** Previously OPEN. Lean module `GroupApproximation/ClassTransposition/Presentation/Coxeter.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-kourovka61.

**First errors (verbatim).**

```
error: GroupApproximation/ClassTransposition/Presentation/Coxeter.lean:183:46: Unknown constant `Equiv.Perm.apply_inv_self`
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Presentation.Coxeter` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
