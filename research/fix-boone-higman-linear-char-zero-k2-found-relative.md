---
rg: 2
id: fix-boone-higman-linear-char-zero-k2-found-relative
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.CharZero.K2Found.Relative: Invalid rewrite argument: The pattern to be substituted is a metavaria"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Relative.lean` is red on main at 296aff5838 (trusted batched probe, Slurm job union build b1789837230). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-linear-char0.


**First errors (verbatim; from probe job direct-b1789839564 on main 9add2d485e).**

```
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Relative.lean:113:25: Invalid rewrite argument: The pattern to be substituted is a metavariable (`?m.207
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Relative.lean:129:25: Invalid rewrite argument: The pattern to be substituted is a metavariable (`?m.460
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Relative.lean:132:14: 'GroupApproximation.BooneHigmanLinear.K2Found.invGen_kills' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/CharZero/K2Found/Relative.lean:151:14: 'GroupApproximation.BooneHigmanLinear.K2Found.invHom_ringMap' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.CharZero.K2Found.Relative` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
