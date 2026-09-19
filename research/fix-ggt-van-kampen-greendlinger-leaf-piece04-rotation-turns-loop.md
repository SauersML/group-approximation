---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-piece04-rotation-turns-loop
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurnsLoop: Type mismatch"
---

**RESOLVED (13d4765e1b, trusted batched probe job direct-b1789850259).** Previously OPEN. Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/RotationTurnsLoop.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/RotationTurnsLoop.lean:101:11: Type mismatch
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/RotationTurnsLoop.lean:227:2: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.facePerm_mem_of_isChain' depends on axioms outside the classical allowli
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/RotationTurnsLoop.lean:229:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.loop_step' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece04/RotationTurnsLoop.lean:232:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns.loop_safeRun' depends on axioms outside the classical allowlist: [sorry
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurnsLoop` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
