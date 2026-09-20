---
rg: 2
id: fix-boone-higman-linear-k2-poly-field-symbol-gen
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.K2Poly.FieldSymbolGen: Unknown identifier bruhatBigCell_act_w_L"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/K2Poly/FieldSymbolGen.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789919140 on main 57f90fce37).**

```
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldSymbolGen.lean:51:9: Unknown identifier `bruhatBigCell_act_w_L`
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldSymbolGen.lean:35:35: unsolved goals
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldSymbolGen.lean:53:14: 'GroupApproximation.BooneHigmanLinear.K2Poly.fsg_small_act' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/K2Poly/FieldSymbolGen.lean:100:14: 'GroupApproximation.BooneHigmanLinear.K2Poly.fsg_of_data' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.K2Poly.FieldSymbolGen` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
