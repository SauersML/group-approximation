---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-step-main
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepMain: (deterministic) timeout at isDefEq, maximum number of heartbeats (2000"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepMain.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepMain.lean:211:76: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepMain.lean:211:59: (deterministic) timeout at `«synthesize pending MVars»`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/StepMain.lean:215:14: 'GroupApproximation.BooneHigmanLinear.BTri.twisted_step' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepMain` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
