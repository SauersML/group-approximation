---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p07-inner-pocket-witness-cu
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistStatement: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/WitnessCurveSublistStatement.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: fix-bh-b.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-ggt-van-kampen-greendlinger-leaf-piece06-predicate`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistStatement` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
