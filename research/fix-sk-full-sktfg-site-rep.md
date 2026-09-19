---
rg: 2
id: fix-sk-full-sktfg-site-rep
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.SiteRep: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/SiteRep.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job direct-b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**Repair landed, unprobed.** 25942699a4: SKTFG: beta-reduce cylinder hypotheses and replace no-op congr steps (unprobed). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**Inputs (nearest red imports).** `fix-sk-full-main-theorem-proof-sentences`, `fix-sk-full-stepanov-matui-matui-tower-coords`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.SiteRep` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
