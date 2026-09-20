---
rg: 2
id: fix-ggt-van-kampen-surgery-path-ribbon
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.SurgeryPathRibbon: Application type mismatch: The argument"
---

**RESOLVED (eae37b23a2, trusted batched probe job direct-b1789842431).** Previously OPEN. Lean module `GroupApproximation/GGT/VanKampen/SurgeryPathRibbon.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.


**First errors (verbatim).**

```
error: GroupApproximation/GGT/VanKampen/SurgeryPathRibbon.lean:151:68: Application type mismatch: The argument
error: GroupApproximation/GGT/VanKampen/SurgeryPathRibbon.lean:233:68: Application type mismatch: The argument
error: GroupApproximation/GGT/VanKampen/SurgeryPathRibbon.lean:358:14: 'GroupApproximation.GGT.VanKampen.PathRibbon.stepEdge' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/GGT/VanKampen/SurgeryPathRibbon.lean:359:14: 'GroupApproximation.GGT.VanKampen.PathRibbon.stepMono' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.SurgeryPathRibbon` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
