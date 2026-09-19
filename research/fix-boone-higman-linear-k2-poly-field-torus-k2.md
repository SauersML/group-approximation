---
rg: 2
id: fix-boone-higman-linear-k2-poly-field-torus-k2
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.K2Poly.FieldTorusK2: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/K2Poly/FieldTorusK2.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.


**First errors (verbatim; from probe job direct-b1789850259 on main 13d4765e1b).**

```
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldTorusK2.lean:41:21: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.K2Poly.FieldTorusK2` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
