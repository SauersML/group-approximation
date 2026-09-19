---
rg: 2
id: fix-class-transposition-presentation-rel-fc
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Presentation.RelFC: This simp argument is unused:"
---

**OPEN.** Lean module `GroupApproximation/ClassTransposition/Presentation/RelFC.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/ClassTransposition/Presentation/RelFC.lean:61:48: This simp argument is unused:
error: GroupApproximation/ClassTransposition/Presentation/RelFC.lean:61:69: This simp argument is unused:
error: GroupApproximation/ClassTransposition/Presentation/RelFC.lean:87:60: omega could not prove the goal:
error: GroupApproximation/ClassTransposition/Presentation/RelFC.lean:136:6: don't know how to synthesize implicit argument `U`
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Presentation.RelFC` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
