---
rg: 2
id: fix-boone-higman-linear-tulenbaev-horrocks-statements
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Statements: bad import 'GroupApproximation.BooneHigmanLinear.Tulenbaev.Components'"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Statements.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789846523 on main b576f069a9).**

```
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Statements.lean:145:53: Unknown constant `IsLocalRing.ResidueField`
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Statements.lean:148:14: 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.StLocalHorrocksFRStatementAt' depends on axioms outside the classical allowlist: [sorryAx]
```


**What it needs.** Make `GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Statements` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
