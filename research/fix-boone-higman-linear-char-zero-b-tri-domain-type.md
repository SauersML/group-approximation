---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-domain-type
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainType: automatically included section variable(s) unused in theorem GroupAppr"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:45:8: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.coe_pU`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:54:8: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigmanLinear.BTri.coe_unitsMap`:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:147:2: Tactic `simp` failed with a nested error:
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/DomainType.lean:149:14: 'GroupApproximation.BooneHigmanLinear.BTri.pval_mul' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainType` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
