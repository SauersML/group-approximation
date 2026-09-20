---
rg: 2
id: fix-boone-higman-linear-tulenbaev-horrocks-field
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Field: bad import 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Sta"
---

**RESOLVED (516e496a4a, trusted batched probe job direct-b1789910605).** Previously OPEN. Lean module `GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Field.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.




**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Field.lean: bad import 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Statements'
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Field.lean: bad import 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Statements'
```

**Inputs (nearest red imports).** `fix-boone-higman-linear-tulenbaev-horrocks-statements`. Fix those first: errors here may be knock-on.

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Field` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
