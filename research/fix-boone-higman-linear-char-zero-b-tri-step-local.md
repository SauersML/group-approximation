---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-step-local
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepLocal: (deterministic) timeout at whnf, maximum number of heartbeats (200000)"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepLocal.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepLocal.lean:126:4: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepLocal.lean:129:5: Function expected at
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepLocal.lean:221:6: Type mismatch
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepLocal.lean:237:14: 'GroupApproximation.BooneHigmanLinear.BTri.slConj_twist' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepLocal` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
