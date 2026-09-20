---
rg: 2
id: fix-class-transposition-presentation-list-crt
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Presentation.ListCrt: Unknown constant Int.emod_add_ediv"
---

**OPEN.** Lean module `GroupApproximation/ClassTransposition/Presentation/ListCrt.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/ClassTransposition/Presentation/ListCrt.lean:149:14: Unknown constant `Int.emod_add_ediv`
error: GroupApproximation/ClassTransposition/Presentation/ListCrt.lean:160:25: Unknown identifier `length_real`
error: GroupApproximation/ClassTransposition/Presentation/ListCrt.lean:159:66: unsolved goals
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Presentation.ListCrt` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
