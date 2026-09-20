---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p05-outer-cell-crossing
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.Crossing: Tactic rewrite failed: motive is not type correct:"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05OuterCell/Crossing.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05OuterCell/Crossing.lean:99:20: Tactic `rewrite` failed: motive is not type correct:
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05OuterCell/Crossing.lean:224:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.targetHead' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05OuterCell/Crossing.lean:225:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.cross_regionCandidate_true' depends on axioms outside the classical allowlist: [sorr
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P05OuterCell/Crossing.lean:226:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.cross_regionCandidate' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.Crossing` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
