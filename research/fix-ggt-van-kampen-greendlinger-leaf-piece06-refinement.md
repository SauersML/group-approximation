---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-piece06-refinement
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Refinement: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Refinement.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job 1290512 on main 1f7bd2d0fe).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Refinement.lean:235:31: Application type mismatch: The argument
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Refinement.lean:237:48: Application type mismatch: The argument
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Refinement.lean:252:14: 'GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RotationRefinement.edgeInsertion' depends on axioms outside the classical allowlist: [sorryA
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Refinement` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
