---
rg: 2
id: fix-boone-higman-linear-char-zero-k2-found-vd-k-row-col
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKRowCol: (deterministic) timeout at whnf, maximum number of heartbeats (200000)"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/K2Found/VdKRowCol.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/VdKRowCol.lean:422:9: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/VdKRowCol.lean:492:14: 'GroupApproximation.BooneHigmanLinear.K2Found.VdK.conj_rowProd' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/VdKRowCol.lean:519:9: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/VdKRowCol.lean:590:14: 'GroupApproximation.BooneHigmanLinear.K2Found.VdK.conj_colProd' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKRowCol` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
