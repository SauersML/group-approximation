---
rg: 2
id: fix-sk-leavitt-fp-k2-refinement-descend
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementDescend: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/K2RefinementDescend.lean` is red on main at eae37b23a2 (trusted batched probe, Slurm job direct-b1789842431). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/K2RefinementDescend.lean:84:35: unsolved goals
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/K2RefinementDescend.lean:102:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineGen_kills_relations' depends on axioms outside the classical allowlist: [so
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/K2RefinementDescend.lean:103:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineHom' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/K2RefinementDescend.lean:104:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.refineHom_x' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementDescend` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
