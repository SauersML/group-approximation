---
rg: 2
id: fix-boone-higman-linear-rel-gen-tits
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.RelGen.Tits: Type mismatch"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/RelGen/Tits.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/BooneHigmanLinear/RelGen/Tits.lean:97:4: Type mismatch
error: GroupApproximation/BooneHigmanLinear/RelGen/Tits.lean:98:6: No goals to be solved
error: GroupApproximation/BooneHigmanLinear/RelGen/Tits.lean:119:14: 'GroupApproximation.BooneHigmanLinear.RelGen.conj_ab_mem_zAll' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/RelGen/Tits.lean:128:14: 'GroupApproximation.BooneHigmanLinear.RelGen.conj_self_z_mem_zAll' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.RelGen.Tits` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
