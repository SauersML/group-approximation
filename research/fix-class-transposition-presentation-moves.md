---
rg: 2
id: fix-class-transposition-presentation-moves
kind: claim
title: "Fix GroupApproximation.ClassTransposition.Presentation.Moves: Not a definitional equality: the left-hand side"
---

**RESOLVED (13d4765e1b, trusted batched probe job direct-b1789850259).** Previously OPEN. Lean module `GroupApproximation/ClassTransposition/Presentation/Moves.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: unowned.

**First errors (verbatim).**

```
error: GroupApproximation/ClassTransposition/Presentation/Moves.lean:39:0: Not a definitional equality: the left-hand side
error: GroupApproximation/ClassTransposition/Presentation/Moves.lean:40:49: Type mismatch
error: GroupApproximation/ClassTransposition/Presentation/Moves.lean:46:2: Type mismatch
error: GroupApproximation/ClassTransposition/Presentation/Moves.lean:116:8: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

**What it needs.** Make `GroupApproximation.ClassTransposition.Presentation.Moves` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
