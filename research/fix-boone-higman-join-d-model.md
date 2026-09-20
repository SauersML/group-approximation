---
rg: 2
id: fix-boone-higman-join-d-model
kind: claim
title: "Fix GroupApproximation.BooneHigman.Join.DModel: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Join/DModel.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Join/DModel.lean:194:60: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Join/DModel.lean:195:53: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Join/DModel.lean:197:14: 'GroupApproximation.BooneHigman.Join.shHom_mem_RW' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigman/Join/DModel.lean:208:30: Application type mismatch: The argument
```

**What it needs.** Make `GroupApproximation.BooneHigman.Join.DModel` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
