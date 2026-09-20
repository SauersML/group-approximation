---
rg: 2
id: fix-ggt-van-kampen-greendlinger-leaf-p01-object-changes-proof
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.Proof: failed to synthesize instance of type class"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01ObjectChanges/Proof.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01ObjectChanges/Proof.lean:61:25: failed to synthesize instance of type class
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01ObjectChanges/Proof.lean:62:43: failed to synthesize instance of type class
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01ObjectChanges/Proof.lean:63:34: failed to synthesize instance of type class
error: GroupApproximation/GGT/VanKampen/GreendlingerLeaf/P01ObjectChanges/Proof.lean:64:31: failed to synthesize instance of type class
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.Proof` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
