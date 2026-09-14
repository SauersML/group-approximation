---
rg: 2
id: higher-rank-lattice-normal-subgroups-central-or-finite-index
kind: claim
title: Normal subgroups of irreducible lattices in higher-rank semisimple Lie groups have finite index or lie in the center
distinct_from:
  normal-subgroups-of-arithmetic-lattices-are-congruence-open: that is openness of the congruence closure of a nontrivial normal subgroup of a torsion-free arithmetic group; this is Margulis's dichotomy between finite index and central normal subgroups.
  mf-kazhdan-groups-with-normal-subgroup-property-are-hyperlinear: that consumes a normal subgroup property to get hyperlinearity of MF Kazhdan groups; this imports the normal subgroup theorem itself for higher-rank lattices.
---

**ESTABLISHED by citation** (`higher-rank-lattice-nst-citation`).

All normal subgroups of irreducible lattices in higher-rank semisimple Lie
groups are either of finite index or contained in the center (Margulis's
normal subgroup theorem).

**Form used in this repository.** Let `n >= 2` and let `L` be a finite-index
subgroup of `Sp_2n(Z)`. `Sp_2n(R)` is a connected simple real Lie group of
real rank `n >= 2` with center `{+1, -1}`. `Sp_2n(Z)` is an arithmetic lattice
in it, as recorded in `deligne-universal-cover-lattice-is-non-rf-kazhdan`,
item 2, so `L` is a lattice, and it is irreducible because the ambient group is
simple. So every normal subgroup `N` of `L` either has finite index in `L` or
is contained in `{+1, -1}`.

**Trust surface.** The statement is quoted from a secondary source. Margulis's
book and Witte-Morris's Theorem 17.1 were not read.
