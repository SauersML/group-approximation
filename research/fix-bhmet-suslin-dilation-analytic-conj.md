---
rg: 2
id: fix-bhmet-suslin-dilation-analytic-conj
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticConj: `noncomm_ring` lacks one vanishing product in `suslinDilAn_conj_row`"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/SuslinDilationAnalyticConj.lean` failed to build in bh-pal-wire's direct batch probe b1789834028 (09-19, base a39af618f3, empty overlay; log work/bh-pal-wire/shared/probe-b1789834028-1.log in the swarm workspace; 1 error lines). It became reachable only once bh-pal-wire's wave-2 repairs went green. Its imports built green in that probe, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.

**Repair landed, unprobed.** 2dd8b94c03: BH metabelian: static repairs for the 8 NEW-RED modules of probe b1789834028, with fix nod. Stays OPEN until a trusted probe builds it green.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/SuslinDilationAnalyticConj.lean:59:67: unsolved goals
```

**Kind.** proof gap (mechanical): the residual goal contains `single p l (c*y) * single p q c`, which vanishes because `l ≠ p`, and that fact was not among the `noncomm_ring` hypotheses.


**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticConj` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
