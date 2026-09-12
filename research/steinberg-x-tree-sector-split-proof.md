---
rg: 2
id: steinberg-x-tree-sector-split-proof
kind: route
title: Separate the A and B exceptional images in the two halves of the spanning tree
target: steinberg-x-row-splits-zero-marginal-tree-sectors
requires:
  - steinberg-fox-chord-actions-are-explicit
  - steinberg-tree-cuts-are-five-marginals
  - steinberg-zero-marginal-space-is-biaffine-circulation
---

By `(STM2)`, `P_f=H_f=0` implies `A_f=C_f=T_f=0`, so `F=E_pf` has zero
coefficient on every tree edge.  The root shears `q,s` preserve the chord
set; consequently `delta_q` and `delta_s` also have zero tree coefficients.

Let `T_1` be the flags whose point lies in `H_0`, and `T_2` the flags whose
plane contains `z`, as in `(SBP2)`.  Applying `A` to a source chord lands in
the tree exactly on `a=-1/2`, and then lands in `T_1\T_2`.  Applying `B` to
a source chord lands in the tree exactly on `c=-1/2`, and then lands in
`T_2\T_1`.  These two output sectors are disjoint.  Since `(SXTS1)` has zero
tree coefficient on its left side, its two right-side tree contributions
must vanish separately.  Restricting `delta_q` and `delta_s` to those source
slices and using `(SMP1)` gives exactly `(SXTS2)`.

After those exceptional source coefficients vanish, both `A delta_q` and
`B delta_s` have no tree support.  They remain Steinberg cycles, so the
tree-cut isomorphism `(SBC3)` and `(STM2)` show that their chord restrictions
separately have zero marginals.

Finally, the inverse image under `A` of a target chord lies in the tree
exactly when the target has `a=1/2`; since `delta_q` vanishes on the tree,
the `A delta_q` coefficient is zero there.  The analogous denominator in
the `B` formula is `1-c`, so `B delta_s` vanishes on the target hyperplane
`c=1`.  At their intersection both terms in `(SXTS1)` vanish, proving
`(SXTS3)`.
