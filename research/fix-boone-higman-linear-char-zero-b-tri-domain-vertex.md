---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-domain-vertex
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainVertex: automatically included section variable(s) unused in theorem GroupAppr"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainVertex.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainVertex.lean:34:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.vertexOf_eq_of_latOf_eq`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainVertex.lean:46:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.vertexOf_scalar_pow`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainVertex.lean:100:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.pUnit_eq_pU`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainVertex.lean:111:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.coe_stdMat`:
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainVertex` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
