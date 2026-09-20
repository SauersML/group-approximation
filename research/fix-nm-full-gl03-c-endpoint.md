---
rg: 2
id: fix-nm-full-gl03-c-endpoint
kind: claim
title: "Fix GroupApproximation.Manuscript.NonMF.Full.GL03C.Endpoint: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/NonMF/Full/GL03C/Endpoint.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```



**Inputs (nearest red imports).** `fix-ggt-van-kampen-greendlinger-leaf-p01-cell-junction-value-hol`, `fix-ggt-van-kampen-greendlinger-leaf-p01-empty-two-gon-triangle`, `fix-ggt-van-kampen-greendlinger-leaf-p01-object-changes-proof`, `fix-ggt-van-kampen-greendlinger-leaf-p05-cell-hair-doubling`, `fix-ggt-van-kampen-greendlinger-leaf-p05-outer-cell-crossing`, `fix-ggt-van-kampen-greendlinger-leaf-p05-outer-side-rotation`, `fix-ggt-van-kampen-greendlinger-leaf-p05-region-pair-rotation`, `fix-ggt-van-kampen-greendlinger-leaf-p05-spur-rotation`, `fix-ggt-van-kampen-greendlinger-leaf-p10-chord-lift-refinement`, `fix-ggt-van-kampen-greendlinger-leaf-piece04-window-shape-class`, `fix-ggt-van-kampen-greendlinger-leaf-piece04-window-shape-head-s`, `fix-ggt-van-kampen-greendlinger-leaf-piece04-window-shape-window`, `fix-ggt-van-kampen-greendlinger-leaf-piece06-refinement`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.Manuscript.NonMF.Full.GL03C.Endpoint` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
