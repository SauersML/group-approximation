---
rg: 2
id: fix-boone-higman-linear-tulenbaev-horrocks-graded-hom
kind: claim
title: "Fix GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Hom: Tactic split_ifs failed: no if-then-else conditions to split"
---

**OPEN.** Lean module `GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Graded/Hom.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Graded/Hom.lean:74:2: Tactic `split_ifs` failed: no if-then-else conditions to split
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Graded/Hom.lean:90:14: 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.horrB' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Graded/Hom.lean:136:14: 'GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.horrB_induction' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigmanLinear/TulenbaevHorrocks/Graded/Hom.lean:234:35: Invalid rewrite argument: The pattern to be substituted is a metavariable (`?m.45 i j hij ?d 0`) in this equality
```

**What it needs.** Make `GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Hom` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
