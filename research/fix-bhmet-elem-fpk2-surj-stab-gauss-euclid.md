---
rg: 2
id: fix-bhmet-elem-fpk2-surj-stab-gauss-euclid
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabGaussEuclid: Function expected at"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPK2SurjStabGaussEuclid.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789910605 on main 516e496a4a).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2SurjStabGaussEuclid.lean:36:22: Function expected at
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2SurjStabGaussEuclid.lean:41:2: unsolved goals
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2SurjStabGaussEuclid.lean:42:48: This simp argument is unused:
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2SurjStabGaussEuclid.lean:42:62: This simp argument is unused:
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabGaussEuclid` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
