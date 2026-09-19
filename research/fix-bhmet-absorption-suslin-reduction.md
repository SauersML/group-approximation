---
rg: 2
id: fix-bhmet-absorption-suslin-reduction
kind: claim
title: "Fix GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinReduction: failed to synthesize CommRing (Polynomial (Chain.SIntPoly m k))"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman`. It is filed as a claim with no prerequisites, not as a route, because the checker would read a route with no prerequisites as a complete proof.

**OPEN.** Lean module `GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinReduction.lean` failed to build in the trusted gqprobe-lean v4 batch, Slurm job 1328760 (09-18, base d2df12ed9 plus bh-pal-wire's wave-1 overlay; request log gq-slurm/batch-b1789769423-3.log; 5 error lines, including the axiom-guard lines that follow them). Its imports built green in that batch, so this is a leaf: its errors are its own.
It is part of the Cairn fix graph (index `board/FIX-GRAPH.md` in the swarm workspace). Owner: bh-pal-wire. Node written by fix-bh-b.

**First errors (verbatim).**

```
error: GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinReduction.lean:49:8: failed to synthesize instance of type class
error: GroupApproximation/BooneHigman/Metabelian/AbsorptionSuslinReduction.lean:81:8: declaration uses `sorry`
```

**Kind.** instance diamond: `Polynomial (Chain.SIntPoly m k)` takes its semiring structure through `Localization.Away`'s commutative-semiring instance, so no `CommRing` instance is found for it.

**Repair landed, unprobed.** 55aba370a4 (bh-pal-wire) states the one-variable step as `SuslinOneVariableAt (A : Type) [CommRing A] N` over a general ring `A` and instantiates it at `Chain.SIntPoly m k`, so that `A[X]` takes its semiring structure from `CommRing A`. The statement is unchanged up to instance paths. The `declaration uses sorry` at 81:8 comes from the synthesis failure at 49:8 (the source has no `sorry`). fix-bh-b reviewed it statically (09-19) and found nothing further.

**What it needs.** Make `GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinReduction` compile with the repository's `-DwarningAsError=true` settings, changing no statement. Slurm submission has been blocked since 09-18 ~20:55 (state/SLURM-BLOCKED), so no trusted build has run since the repair landed.

**Resolution.** When a trusted probe (gqprobe-lean.sh) builds it green, change the status line above to
`**RESOLVED (<green commit>).**`
