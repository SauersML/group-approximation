---
rg: 2
id: fix-bhmet-elem-fp-char-zero-k2-split
kind: route
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2Split.lean` fails to build on main (trusted MSI build of origin/main 3c8b417428, 09-18; 4 error lines).
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire.
Source changed on main since that build: no.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2Split.lean:110:6: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2Split.lean:129:21: Function expected at
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2Split.lean:134:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2Split.lean:166:8: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split` compile with the repository's `-DwarningAsError=true` settings, changing no statement.
No imported module is red in that build, so this is a leaf: its errors are its own.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`.
