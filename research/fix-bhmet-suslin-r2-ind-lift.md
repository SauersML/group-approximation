---
rg: 2
id: fix-bhmet-suslin-r2-ind-lift
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.SuslinR2IndLift: (deterministic) timeout at whnf, maximum number of heartbeats (200000)"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/SuslinR2IndLift.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789910605 on main 516e496a4a).**

```
error: GroupApproximation/BooneHigman/Metabelian/SuslinR2IndLift.lean:80:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.SuslinR2IndLift` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
