---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p07-inner-pocket-witness-st
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSubStatement: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P07InnerPocket/WitnessStepSubStatement.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: fix-bh-b.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```
























**Inputs (nearest red imports).** `fix-ggt-van-kampen-greendlinger-leaf-piece06-refinement`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSubStatement` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
