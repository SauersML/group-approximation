---
rg: 2
id: fix-sk-boone-higman-higman-step
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.BooneHigman.HigmanStep: typeclass instance problem is stuck"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/BooneHigman/HigmanStep.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-green-sk.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/BooneHigman/HigmanStep.lean:70:65: typeclass instance problem is stuck
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/BooneHigman/HigmanStep.lean:95:82: unexpected identifier; expected '}'
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/BooneHigman/HigmanStep.lean:95:9: Fields missing: `π_surjective`, `re`
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/BooneHigman/HigmanStep.lean:138:14: 'GroupApproximation.SimpleKazhdanSofic.BooneHigman.nonempty_fgRecursive_of_hasSolvableWordProblem' depends on axioms outside the classical allowlist
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.BooneHigman.HigmanStep` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
