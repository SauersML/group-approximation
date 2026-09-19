---
rg: 2
id: fix-bhmet-elem-fpnk2-core-slice
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPNK2CoreSlice: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPNK2CoreSlice.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPNK2CoreSlice.lean:114:4: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/ElemFPNK2CoreSlice.lean:133:2: 'GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_pad_dies_of_sliceOver' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigman/Metabelian/ElemFPNK2CoreSlice.lean:149:2: 'GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_coneOver_of_sliceOver' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPNK2CoreSlice` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
