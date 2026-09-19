---
rg: 2
id: fix-class-transposition-out-counting
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Out.Counting: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/ClassTransposition/Out/Counting.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-kourovka57.

**First errors (verbatim; from probe job direct-b1789837230 on main 296aff5838).**

```
error: GroupApproximation/ClassTransposition/Out/Counting.lean:226:18: Application type mismatch: The argument
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Out.Counting` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
