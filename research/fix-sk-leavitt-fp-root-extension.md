---
rg: 2
id: fix-sk-leavitt-fp-root-extension
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.RootExtension: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/RootExtension.lean` is red on main at eae37b23a2 (trusted batched probe, Slurm job direct-b1789842431). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789910605 on main 516e496a4a).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/RootExtension.lean:48:5: `inferInstanceAs` failed, expected type contains metavariables
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/RootExtension.lean:48:2: expected structure
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/RootExtension.lean:83:2: Type mismatch
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/LeavittFP/RootExtension.lean:191:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.rootSum' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.RootExtension` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
