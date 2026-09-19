---
rg: 2
id: fix-boone-higman-linear-char-zero-k2-found-two-zero
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TwoZero: automatically included section variable(s) unused in theorem GroupAppr"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/K2Found/TwoZero.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/TwoZero.lean:53:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.K2Found.TwoZero.cramerRow_apply_of_ne`:
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/TwoZero.lean:76:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.K2Found.TwoZero.sum_mul_minor_left`:
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/TwoZero.lean:83:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.K2Found.TwoZero.sum_mul_minor_right`:
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/TwoZero.lean:99:77: Unknown constant `Finset.sum_smul`
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TwoZero` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
