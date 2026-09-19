---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p05-region-pair-step-transp
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.StepTransport: failed to synthesize instance of type class"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05RegionPair/StepTransport.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05RegionPair/StepTransport.lean:143:17: failed to synthesize instance of type class
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.StepTransport` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
