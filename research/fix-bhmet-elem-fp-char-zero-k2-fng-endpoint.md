---
rg: 2
id: fix-bhmet-elem-fp-char-zero-k2-fng-endpoint
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngEndpoint: Application type mismatch: The argument"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2FngEndpoint.lean` is red on main at 13d4765e1b (trusted batched probe, job direct-b1789850259). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789912910 on main 4067aaa686).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2FngEndpoint.lean:69:52: Application type mismatch: The argument
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2FngEndpoint.lean:72:2: 'GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2Fng_elemFour_fp_of_rankFourFP' depends on axioms outside the classical allowlist: [sorryAx
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2FngEndpoint.lean:82:14: 'GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRankFour_of_rankFourFP' depends on axioms outside the classical allowlist: [sorryAx]
error: GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2FngEndpoint.lean:115:2: 'GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2Fng_stabGenFNGSurj_of_rankFourFP' depends on axioms outside the classical allowlist: [sor
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngEndpoint` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
