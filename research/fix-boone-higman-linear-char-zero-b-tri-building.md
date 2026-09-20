---
rg: 2
id: fix-boone-higman-linear-char-zero-b-tri-building
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.BTri.Building: Invalid field Connected: The environment does not contain SimpleGraph."
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/CharZero/BTri/Building.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.


**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Building.lean:122:46: Invalid field `Connected`: The environment does not contain `SimpleGraph.Connected`, so it is not possible to project the field `Connected` from an expression
error: GroupApproximation/BooneHigmanLinear/CharZero/BTri/Building.lean:126:14: 'GroupApproximation.BooneHigmanLinear.BTri.BuildingSimplyConnectedStatement' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.BTri.Building` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
