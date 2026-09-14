---
rg: 2
id: reduced-mf-nonsofic-group-dichotomy-proof
kind: route
title: Quotient by the invisible subgroup, bound it by the amenable radical, split on soficity
target: reduced-mf-nonsofic-group-dichotomy
requires: [reduced-mf-hyperlinear-radical-in-amenable-radical, hyperlinear-elementwise-visibility]
---

Let `N` be the intersection of the kernels of all homomorphisms from `G` into
unitary groups of tracial matrix ultraproducts.  As recorded in the proof of
`reduced-mf-hyperlinear-radical-in-amenable-radical`, `N` is exactly the set of
elements that are not tracially visible.

1. **`N` is normal**, as an intersection of kernels.
2. **`N` is amenable.**  By `reduced-mf-hyperlinear-radical-in-amenable-radical`,
   `N <= R_a(G)`, and subgroups of amenable groups are amenable.
3. **`G/N` is hyperlinear.**  Let `gN != N`.  Some homomorphism `rho` into a
   tracial ultraproduct has `rho(g) != 1`.  It kills `N`, so it factors through
   `G/N`, and faithfulness of the trace gives `Re tau(rho(g)) < 1`.  Lifting
   `rho` along the ultrafilter makes `gN` tracially visible in `G/N` with
   constant `(1 - Re tau(rho(g))) / 2`.  By `hyperlinear-elementwise-visibility`,
   `G/N` is hyperlinear.
4. **Split.**  If `G/N` is not sofic, (a) holds.  If `G/N` is sofic, then `G`,
   which is nonsofic by hypothesis, is an extension of the amenable group `N`
   by the sofic group `G/N`, which is (b).  The alternatives are exclusive.
