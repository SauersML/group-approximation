---
rg: 2
id: fix-sk-full-sktfg-stages
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Stages: an impossible interval_cases branch and an unreachable tactic"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/SKTFG/Stages.lean` is red on main at 25942699a4 (union log of batch b1789856358). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: sk-tfg-b.

**Repair landed, unprobed.** e7cefdce2b:
- `consSet_four_cases`: `interval_cases i` also produces the case `i = 3`, where the hypothesis `hj : 3 + 1 < 4` is false. It is now closed with `absurd hj (by norm_num)`.
- `good_left`: the unused alternative `exact (funext hz).symm` in the first `convert` step is removed.

Stays OPEN until a trusted probe builds it green (request 1789863648.40826.sk-tfg-b is queued).

**First errors (verbatim).**

```
Stages.lean:67:28: unsolved goals
case «3»
hi : 3 < 4
hj : 3 + 1 < 4
⊢ P (adjSwap ⟨3, hi⟩ * adjSwap ⟨3 + 1, hj⟩)
```

and `Stages.lean:205:42: this tactic is never executed`. The `sorryAx` reports for `good_step` and `good_left` follow from the first error.

**Inputs.** None red: AltConsecutive and Cylinders are built green in batch b1789856358.

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.Stages` compile under the repository settings without changing any statement. ThreeCycleWitness and the FG chain wait on it.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
