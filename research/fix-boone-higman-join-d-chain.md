---
rg: 2
id: fix-boone-higman-join-d-chain
kind: claim
title: "Fix GroupApproximation.BooneHigman.Join.DChain: Tactic rewrite failed: motive is not type correct:"
---

**RESOLVED (516e496a4a, trusted batched probe job direct-b1789910605).** Previously OPEN. Lean module `GroupApproximation/BooneHigman/Join/DChain.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.


**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Join/DChain.lean:163:18: Tactic `rewrite` failed: motive is not type correct:
error: GroupApproximation/BooneHigman/Join/DChain.lean:169:14: 'GroupApproximation.BooneHigman.Join.K0_pow_maps' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigman/Join/DChain.lean:195:14: 'GroupApproximation.BooneHigman.Join.K0_pow_self' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigman/Join/DChain.lean:237:14: 'GroupApproximation.BooneHigman.Join.telescope' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigman.Join.DChain` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
