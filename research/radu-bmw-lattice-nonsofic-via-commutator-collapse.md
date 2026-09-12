---
rg: 2
id: radu-bmw-lattice-nonsofic-via-commutator-collapse
kind: route
title: Collapse one commutator in every almost action, then the mark collapses
target: radu-bmw-lattice-nonsofic
requires:
  - radu-commutator-collapse
  - radu-mark-is-controlled-by-one-commutator
---

Suppose `Gamma_R` were sofic.

1. A sofic approximation gives permutation almost actions whose relator
   defects tend to zero and which separate the nontrivial element `(xz)^4`.
   The element is nontrivial because `x,z` generate an infinite dihedral
   subgroup of `<x,y,z> = C_2*C_2*C_2`.
2. Each approximate involution `sigma` can be replaced by an exact involution
   at normalized Hamming distance at most `d_H(sigma^2,1)`: keep `sigma` on
   its invariant set `{p : sigma^2 p = p}` and fix the other points.  Every
   fixed word then changes by `o(1)`.
3. On the modified sequence `radu-commutator-collapse` gives
   `kappa1 -> 0`, and `(RL1)` of `radu-mark-is-controlled-by-one-commutator`
   gives `d_H((xz)^4,1) -> 0`.

This contradicts separation, so `Gamma_R` is not sofic.
