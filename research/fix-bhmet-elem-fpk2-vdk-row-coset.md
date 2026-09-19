---
rg: 2
id: fix-bhmet-elem-fpk2-vdk-row-coset
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCoset: whnf timeout in `vdkRowCosetEquiv_col`"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/ElemFPK2VdKRowCoset.lean` failed to build in bh-pal-wire's direct batch probe b1789834028 (09-19, base a39af618f3, empty overlay; log work/bh-pal-wire/shared/probe-b1789834028-1.log in the swarm workspace; 2 error lines). It became reachable only once bh-pal-wire's wave-2 repairs went green. Its imports built green in that probe, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: fix-bh-b.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2VdKRowCoset.lean:97:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
error: GroupApproximation/BooneHigman/Metabelian/ElemFPK2VdKRowCoset.lean:110:18: (kernel) unknown constant 'GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetEquiv_col'
```

**Kind.** elaboration performance: the `change` to `colRoot i a * …` forces a definitional unfolding of `colRoot` against `(vdkRowCanonical n R).col` and `vdkRowCosetEquiv`, which hits the 200000-heartbeat limit. The unknown constant at 110 follows.

**Repair landed, unprobed.** fix-bh-b replaces the `change` with three rewriting facts proved by `simp only`: `hc` unfolds `vdkRowCanonical` to its `col` field, and `hl`/`hr` unfold `vdkRowCosetEquiv`, `Equiv.ofBijective_apply`, `vdkCol_apply` and `vdkRowCosetMap_apply`. Then `rw [hl, hr, hc, vdkRowPar_col, mul_assoc]`. No heartbeat increase.

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCoset` compile with the repository's `-DwarningAsError=true` settings, changing no statement.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
