---
rg: 2
id: fix-sk-halfline-b-represent
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Represent: dsimp made no progress"
---

**OPEN.** Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/HalflineB/Represent.lean` is red on main at 463f140e0d (trusted batched probe, Slurm job 1398755). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/HalflineB/Represent.lean:163:2: `dsimp` made no progress
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/HalflineB/Represent.lean:224:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.exists_hMat_eq' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Represent` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
