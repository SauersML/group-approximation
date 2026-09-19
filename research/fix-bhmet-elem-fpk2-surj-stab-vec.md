---
rg: 2
id: fix-bhmet-elem-fpk2-surj-stab-vec
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabVec: fails through red imports"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPK2SurjStabVec.lean` is red on main at 9add2d485e (trusted batched probe, Slurm job direct-b1789839564). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.


**Repair landed, unprobed.** 283f248812: ElemFPK2SurjStabVec: omit [Ring R] on surjStabVec_inj (unprobed). Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
(none in this file: it fails only because red imports fail; see Inputs)
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabVec` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
