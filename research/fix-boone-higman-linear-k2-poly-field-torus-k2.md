---
rg: 2
id: fix-boone-higman-linear-k2-poly-field-torus-k2
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.K2Poly.FieldTorusK2: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/K2Poly/FieldTorusK2.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**Repair landed, unprobed.** 7c8da9d7f0: Fix projection_h_mul in K2Poly/FieldTorusK2. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldTorusK2.lean:33:92: unsolved goals
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldTorusK2.lean:41:22: This simp argument is unused:
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldTorusK2.lean:43:14: 'GroupApproximation.BooneHigmanLinear.K2Poly.projection_h_mul' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldTorusK2.lean:54:14: 'GroupApproximation.BooneHigmanLinear.K2Poly.symbol_mem_K2' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.K2Poly.FieldTorusK2` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
