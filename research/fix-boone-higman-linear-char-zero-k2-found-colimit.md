---
rg: 2
id: fix-boone-higman-linear-char-zero-k2-found-colimit
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.K2Found.Colimit: Type mismatch"
---

**RESOLVED (13d4765e1b, trusted batched probe job direct-b1789850259).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Colimit.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.



**First errors (verbatim; from probe job direct-b1789839564 on main 9add2d485e).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Colimit.lean:68:18: Type mismatch
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Colimit.lean:74:2: Type mismatch
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Colimit.lean:74:27: Application type mismatch: The argument
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Colimit.lean:76:14: 'GroupApproximation.BooneHigmanLinear.K2Found.stOf_le' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.K2Found.Colimit` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
