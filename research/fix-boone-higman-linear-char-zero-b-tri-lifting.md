---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-lifting
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.Lifting: List.getLast?_eq_getLast has been deprecated: Use List.getLast?_eq_som"
---

**RESOLVED (516e496a4a, trusted batched probe job direct-b1789910605).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/Lifting.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.


**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Lifting.lean:279:8: `List.getLast?_eq_getLast` has been deprecated: Use `List.getLast?_eq_some_getLast` instead
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Lifting.lean:282:14: This simp argument is unused:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Lifting.lean:302:24: `SimpleGraph.Walk.support_eq_cons` has been deprecated: Use `SimpleGraph.Walk.cons_tail_support` instead
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Lifting.lean:305:22: `SimpleGraph.Walk.support_eq_cons` has been deprecated: Use `SimpleGraph.Walk.cons_tail_support` instead
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.Lifting` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
