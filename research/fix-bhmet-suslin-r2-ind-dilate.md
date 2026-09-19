---
rg: 2
id: fix-bhmet-suslin-r2-ind-dilate
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.SuslinR2IndDilate: (deterministic) timeout at whnf, maximum number of heartbeats (200000)"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/SuslinR2IndDilate.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.


**Repair landed, unprobed.** ed7f648b07: BH chain wave 5: static fixes for bh-pal-wires reds in union build b1789839564 (unprobed). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/SuslinR2IndDilate.lean:74:56: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigman/Metabelian/SuslinR2IndDilate.lean:76:14: 'GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_mem_of_dilate' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.SuslinR2IndDilate` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
