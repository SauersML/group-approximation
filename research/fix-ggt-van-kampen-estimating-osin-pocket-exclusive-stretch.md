---
rg: 2
id: fix-ggt-van-kampen-estimating-osin-pocket-exclusive-stretch
kind: claim
title: "Fix GroupApproximation.GGT.VanKampen.Estimating.OsinPocketExclusiveStretch: Unknown identifier q"
---

**OPEN.** Lean module `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketExclusiveStretch.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: non-MF). Owner: ms-green-nm.

**First errors (verbatim).**

```
error: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketExclusiveStretch.lean:194:63: Unknown identifier `q`
error: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketExclusiveStretch.lean:194:66: unsolved goals
error: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketExclusiveStretch.lean:248:14: 'GroupApproximation.GGT.VanKampen.ExclusiveStretch.isChain_leftStretch'' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.GGT.VanKampen.Estimating.OsinPocketExclusiveStretch` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
