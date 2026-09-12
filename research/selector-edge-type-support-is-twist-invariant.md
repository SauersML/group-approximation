---
rg: 2
id: selector-edge-type-support-is-twist-invariant
kind: claim
title: A selector-free common edge type sees whole affine twist orbits of assignments
distinct_from:
  finite-packet-central-sign-cannot-enforce-nonlinear-support: that obtains every marked assignment; this measures exactly which selector quotient an edge type retains.
  selector-free-spin-reset-leaves-contexts-independent: that is one reset countermodel; this is the general twist theorem.
  gauge-doubling-gives-selector-flip-symmetries: that supplies gauge symmetry; this proves it does not reduce logical selector rank.
---

Let `A<=L` be an elementary abelian selector subgroup, `E<=L`, and fix an
irreducible `E`-type `sigma`.  The union `R_sigma` of `A`-weights in all
irreducible `L`-representations containing `sigma` is invariant under every
selector character extending to `L` trivially on `E`.

Hence a common edge type selects only a union of affine twist orbits.  In a
direct-product selector packet, exact support on a truth set `R` forces the
edge to retain at least
`rank(A)-rank(Stab(R))` logical selector directions.  Gauge doubling adds
only the private gauge kernel and leaves this logical rank unchanged.
