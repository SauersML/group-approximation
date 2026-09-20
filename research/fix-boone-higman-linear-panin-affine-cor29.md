---
rg: 2
id: fix-boone-higman-linear-panin-affine-cor29
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.




**First errors (verbatim; from probe job direct-b1789919140 on main 57f90fce37).**

```
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:375:2: Type mismatch
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:382:6: Type mismatch
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:385:14: 'GroupApproximation.BooneHigmanLinear.PaninAffine.kappa0' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/PaninAffine/Cor29.lean:391:14: 'GroupApproximation.BooneHigmanLinear.PaninAffine.kappa' depends on axioms outside the classical allowlist: [sorryAx]
```


**What it needs.** Make `GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
