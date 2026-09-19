---
rg: 2
id: fix-bhmet-elem-fp-char-zero-sl-four-fp-int-pres
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPIntPres: automatically included section variable(s) unused in theorem GroupAppr"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroSLFourFPIntPres.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789850259 on main 13d4765e1b).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroSLFourFPIntPres.lean:59:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_intGroup_isFinitelyP
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroSLFourFPIntPres.lean:68:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_y_commute`:
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroSLFourFPIntPres.lean:78:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_y_commutator`:
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPIntPres` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
