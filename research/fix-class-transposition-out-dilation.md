---
rg: 2
id: fix-class-transposition-out-dilation
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Out.Dilation: unexpected token '('; expected ')', ',' or ':'"
---

**OPEN.** Lean module `GroupApproximation/ClassTransposition/Out/Dilation.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-kourovka57.

**First errors (verbatim; from probe job direct-b1789837230 on main 296aff5838).**

```
error: GroupApproximation/ClassTransposition/Out/Dilation.lean:88:82: unexpected token '('; expected ')', ',' or ':'
error: GroupApproximation/ClassTransposition/Out/Dilation.lean:88:43: Type mismatch
error: GroupApproximation/ClassTransposition/Out/Dilation.lean:54:52: unsolved goals
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Out.Dilation` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
