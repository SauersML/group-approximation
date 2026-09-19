---
rg: 2
id: fix-class-transposition-presentation-presented
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Presentation.Presented: No goals to be solved"
---

**RESOLVED (b576f069a9, trusted batched probe job direct-b1789846523).** Previously OPEN. Lean module `GroupApproximation/ClassTransposition/Presentation/Presented.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.


**First errors (verbatim).**

```
error: GroupApproximation/ClassTransposition/Presentation/Presented.lean:100:4: No goals to be solved
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Presentation.Presented` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
