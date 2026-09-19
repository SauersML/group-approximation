---
rg: 2
id: fix-boone-higman-linear-tulenbaev-components
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.Tulenbaev.Components: bad import 'Mathlib.RingTheory.Localization.AtPrime'"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/Tulenbaev/Components.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**Repair landed, unprobed.** a8ae0e7e93: Fix the Tulenbaev Components import and add the local–global reduction. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/Tulenbaev/Components.lean: bad import 'Mathlib.RingTheory.Localization.AtPrime'
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.Tulenbaev.Components` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
