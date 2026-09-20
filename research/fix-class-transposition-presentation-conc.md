---
rg: 2
id: fix-class-transposition-presentation-conc
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Presentation.Conc: Unknown identifier lev_split"
---

**OPEN.** Lean module `GroupApproximation/ClassTransposition/Presentation/Conc.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/ClassTransposition/Presentation/Conc.lean:34:34: Unknown identifier `lev_split`
error: GroupApproximation/ClassTransposition/Presentation/Conc.lean:74:8: Unknown identifier `lev_split`
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Presentation.Conc` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
