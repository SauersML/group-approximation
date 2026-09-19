---
rg: 2
id: fix-boone-higman-join-assoc
kind: claim
title: "Fix GroupApproximation.BooneHigman.Join.Assoc: Unknown identifier higSw_lift_nil"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Join/Assoc.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Join/Assoc.lean:259:15: Unknown identifier `higSw_lift_nil`
error: GroupApproximation/BooneHigman/Join/Assoc.lean:257:63: unsolved goals
error: GroupApproximation/BooneHigman/Join/Assoc.lean:261:14: 'GroupApproximation.BooneHigman.Join.jPhi_nil' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigman/Join/Assoc.lean:278:14: 'GroupApproximation.BooneHigman.Join.jPhi_mem_Phi' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigman.Join.Assoc` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
