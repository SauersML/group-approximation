---
rg: 2
id: fix-bhmet-elem-fpk2-poly-deg-kernel
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegKernel: invalid ▸ notation, argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPK2PolyDegKernel.lean` is red on main at b576f069a9 (trusted batched probe, job direct-b1789846523). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2PolyDegKernel.lean:90:45: invalid `▸` notation, argument
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2PolyDegKernel.lean:89:89: unsolved goals
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2PolyDegKernel.lean:122:14: 'GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_eq_one_of_mem_P' depends on axioms outside the classical allowlist: [sorryAx]
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegKernel` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
