---
rg: 2
id: fix-boone-higman-linear-tulenbaev-local-global
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.Tulenbaev.LocalGlobal: unknown tactic"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/Tulenbaev/LocalGlobal.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/Tulenbaev/LocalGlobal.lean:213:9: unknown tactic
error: GroupApproximation/BooneHigmanLinear/Tulenbaev/LocalGlobal.lean:210:65: unsolved goals
error: GroupApproximation/BooneHigmanLinear/Tulenbaev/LocalGlobal.lean:209:4: unsolved goals
error: GroupApproximation/BooneHigmanLinear/Tulenbaev/LocalGlobal.lean:151:83: unsolved goals
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.Tulenbaev.LocalGlobal` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
