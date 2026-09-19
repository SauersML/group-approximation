---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p10-local-select-statement
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Statement: fails through red imports"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10LocalSelect/Statement.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job direct-b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: nm-gl03d.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-ggt-van-kampen-greendlinger-leaf-p10-filter-move-exists-colo`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Statement` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
