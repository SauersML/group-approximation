---
rg: 2
id: fix-thompson-ore-normal-form
kind: claim
title: "Fix GroupApproximation.ThompsonOre.NormalForm: failed to synthesize instance of type class"
---

**RESOLVED (1f7bd2d0fe, trusted batched probe job 1290512).** Previously OPEN. Lean module `GroupApproximation/ThompsonOre/NormalForm.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-integrate.


**First errors (verbatim).**

```
error: GroupApproximation/ThompsonOre/NormalForm.lean:154:32: failed to synthesize instance of type class
error: GroupApproximation/ThompsonOre/NormalForm.lean:154:59: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

**What it needs.** Make `GroupApproximation.ThompsonOre.NormalForm` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
