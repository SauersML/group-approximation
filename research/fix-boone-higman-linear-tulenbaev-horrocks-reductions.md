---
rg: 2
id: fix-boone-higman-linear-tulenbaev-horrocks-reductions
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Reductions: Tactic rewrite failed: Did not find an occurrence of the pattern"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Reductions.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Reductions.lean:281:73: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Reductions.lean:293:14: 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksAt_of_localGlobal' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Reductions.lean:300:14: 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stHorrocksStatement_of' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Reductions.lean:375:14: 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.stMonicInjStatement_of' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Reductions` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
