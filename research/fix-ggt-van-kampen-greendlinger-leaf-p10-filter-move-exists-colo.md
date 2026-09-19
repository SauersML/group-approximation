---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p10-filter-move-exists-colo
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.Colour: failed to synthesize instance of type class"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10FilterMoveExists/Colour.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job direct-b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.


**First errors (verbatim; from probe job direct-b1789837230 on main 296aff5838).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10FilterMoveExists/Colour.lean:60:8: failed to synthesize instance of type class
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10FilterMoveExists/Colour.lean:63:2: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_eq_true_iff' depends on axioms outside the classical allowlist: [s
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10FilterMoveExists/Colour.lean:70:2: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_eq_false_iff' depends on axioms outside the classical allowlist: [
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P10FilterMoveExists/Colour.lean:82:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.p10FM_z_congr' depends on axioms outside the classical allowlist: [sorryA
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10FilterMoveExists.Colour` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
