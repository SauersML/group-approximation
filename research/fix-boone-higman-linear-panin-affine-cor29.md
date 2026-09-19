---
rg: 2
id: fix-boone-higman-linear-panin-affine-cor29
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.


**First errors (verbatim; from probe job direct-b1789850259 on main 13d4765e1b).**

```
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:151:20: Application type mismatch: The argument
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:154:14: 'GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29FinitaryAt' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:374:4: Application type mismatch: The argument
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:377:14: 'GroupApproximation.BooneHigmanLinear.PaninAffine.kappa0' depends on axioms outside the classical allowlist: [sorryAx]
```


**What it needs.** Make `GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
