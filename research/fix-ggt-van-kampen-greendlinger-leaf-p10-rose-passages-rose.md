---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p10-rose-passages-rose
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.Rose: fails through red imports"
---

**RESOLVED (13d4765e1b, trusted batched probe job direct-b1789850259).** Previously OPEN. Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10RosePassages/Rose.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: unowned.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-ggt-van-kampen-greendlinger-leaf-p10-filter-move-exists-colo`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RosePassages.Rose` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
