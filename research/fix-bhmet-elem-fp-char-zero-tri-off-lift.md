---
rg: 2
id: fix-bhmet-elem-fp-char-zero-tri-off-lift
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffLift: Type mismatch"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroTriOffLift.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789919140 on main 57f90fce37).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroTriOffLift.lean:97:67: Type mismatch
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroTriOffLift.lean:102:14: 'GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_T_mem' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffLift` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
