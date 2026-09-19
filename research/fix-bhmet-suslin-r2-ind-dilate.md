---
rg: 2
id: fix-bhmet-suslin-r2-ind-dilate
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.SuslinR2IndDilate: (deterministic) timeout at whnf, maximum number of heartbeats (200000)"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/SuslinR2IndDilate.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.



**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/BooneHigman/Metabelian/SuslinR2IndDilate.lean:75:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.SuslinR2IndDilate` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
