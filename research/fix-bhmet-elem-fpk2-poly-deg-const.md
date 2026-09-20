---
rg: 2
id: fix-bhmet-elem-fpk2-poly-deg-const
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegConst: (deterministic) timeout at isDefEq, maximum number of heartbeats (2000"
---

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPK2PolyDegConst.lean` is red on main at 516e496a4a (trusted batched probe, job direct-b1789910605). It is not in the root closure.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace; goal: BH Palomar). Owner: bh-pal-wire.

**First errors (verbatim; from probe job direct-b1789915961 on main 1f7bd2d0fe).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2PolyDegConst.lean:130:73: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2PolyDegConst.lean:110:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegConst` compile under the repository settings without changing any statement.

**Resolution.** When a trusted probe builds it green, change the status line above to `**RESOLVED (<green commit>).**`.
