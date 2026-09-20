---
rg: 2
id: fix-sk-sk-open-hyperbolic-host
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.HyperbolicHost: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/SkOpen/HyperbolicHost.lean` is red on main at 463f140e0d (trusted batched probe, Slurm job 1398755). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-sk-open.



**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```


**Inputs (nearest red imports).** `fix-ggt-van-kampen-greendlinger-leaf-p01-cell-junction-value-hol`, `fix-ggt-van-kampen-greendlinger-leaf-p05-region-pair-rotation`, `fix-nm-full-gl03-d-kept-walk`, `fix-nm-full-gl06b-outer-side-transport`, `fix-nm-full-gl06d-outer-monogon-diagram`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.HyperbolicHost` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
