---
rg: 2
id: fix-boone-higman-linear-ls-core-zc
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.LSCore.ZC: unsolved goals"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/LSCore/ZC.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/BooneHigmanLinear/LSCore/ZC.lean:115:76: unsolved goals
error: GroupApproximation/BooneHigmanLinear/LSCore/ZC.lean:124:14: 'GroupApproximation.BooneHigmanLinear.LSCore.z_conj_obtuse_row' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/LSCore/ZC.lean:129:73: unsolved goals
error: GroupApproximation/BooneHigmanLinear/LSCore/ZC.lean:137:14: 'GroupApproximation.BooneHigmanLinear.LSCore.z_conj_obtuse_col' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.LSCore.ZC` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
