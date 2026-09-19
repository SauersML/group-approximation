---
rg: 2
id: fix-sk-halfline-b-decide
kind: claim
title: "Fix GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Decide: Tactic rewrite failed: Did not find an occurrence of the pattern"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/Manuscript/SimpleKazhdanSofic/HalflineB/Decide.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: SK). Owner: ms-green-sk.


**First errors (verbatim).**

```
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/HalflineB/Decide.lean:76:55: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/HalflineB/Decide.lean:396:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.tabOk_iff' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/Manuscript/SimpleKazhdanSofic/HalflineB/Decide.lean:397:14: 'GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.wordValue_eq_one_iff_matOk' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Decide` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
