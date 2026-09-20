---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-piece06-predicate
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Predicate: failed to synthesize instance of type class"
---

**RESOLVED (516e496a4a, trusted batched probe job direct-b1789910605).** Previously OPEN. Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Predicate.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.


**First errors (verbatim; from probe job direct-b1789850259 on main 13d4765e1b).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Predicate.lean:96:59: failed to synthesize instance of type class
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Predicate.lean:98:60: failed to synthesize instance of type class
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Predicate.lean:99:11: failed to synthesize instance of type class
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/Piece06/Predicate.lean:105:24: failed to synthesize instance of type class
```


**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Predicate` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
