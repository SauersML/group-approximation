---
rg: 2
id: fix-boone-higman-linear-rel-gen-z-tools
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.RelGen.ZTools: Unknown constant Polynomial.mem_map_C_iff"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/RelGen/ZTools.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/BooneHigmanLinear/RelGen/ZTools.lean:114:19: Unknown constant `Polynomial.mem_map_C_iff`
error: GroupApproximation/BooneHigmanLinear/RelGen/ZTools.lean:121:14: 'GroupApproximation.BooneHigmanLinear.RelGen.sub_C_evalZero_mem_xPolyIdeal' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.RelGen.ZTools` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
