---
rg: 2
id: fix-boone-higman-linear-char-zero-k2-found-rel-pres
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPres: Unknown constant Ideal.sum_mem"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPres.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**Repair landed, unprobed.** d792c9f8ad: Z1-base, K2Found: fix Lifting, TwoZero, RelPres from probe b1789850259; TulXa imports. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPres.lean:94:8: Unknown constant `Ideal.sum_mem`
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPres.lean:96:14: 'GroupApproximation.BooneHigmanLinear.K2Found.RelPres.vecMul_mem' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/RelPres.lean:108:14: 'GroupApproximation.BooneHigmanLinear.K2Found.RelPres.smulPair_mem' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPres` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
