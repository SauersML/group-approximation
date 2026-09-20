---
rg: 2
id: fix-boone-higman-linear-char-zero-k2-found-rel-pres-act
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresAct: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPresAct.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPresAct.lean:39:68: Application type mismatch: The argument
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPresAct.lean:40:64: Application type mismatch: The argument
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPresAct.lean:72:14: 'GroupApproximation.BooneHigmanLinear.K2Found.RelPres.actGen_kills' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPresAct.lean:82:14: 'GroupApproximation.BooneHigmanLinear.K2Found.RelPres.actEnd_X' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresAct` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
