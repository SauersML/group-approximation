---
rg: 2
id: sl3-large-prime-collapse-from-hnn-matrix-range
kind: route
title: Exactify only HNN-selected lattice tuples and apply the closed large-prime face
target: sl3-large-prime-pair-relative-commutant-collapse
requires:
  - sl3-large-prime-hnn-matrix-range-capture
  - kazhdan-generator-matrix-range-capture-exactifies
  - kazhdan-subgroup-weak-ucp-exactifies-microstates
  - p-divisible-lambda-exact-mass-vanishes-at-large-primes
  - odd-congruence-lambda-exact-sector-collapses
  - coprime-sector-collapse-is-robust-to-small-p-admixture
---

Take a canonical hyperlinear approximation of `G_p`.  The first two inputs
replace its lattice restriction, after vanishing flexible padding, by a
genuine finite-dimensional representation.  The relative exactification
theorem performs this correction without losing the stable-letter relations
or the canonical trace.  Finite-image rigidity and the congruence subgroup
property put the exact lattice representation at a level `p^D m'`.

The depth-free theorem makes its `p`-divisible weight `O(epsilon^2)` for
`p>=11`; the odd/coprime theorem collapses the remaining sector, and robust
absorption removes the vanishing `p`-part.  Hence the stable letter commutes
with the whole S-arithmetic group in the ultraproduct, contradicting its
canonical HNN mixed moment.  This proves `(RC3-p)`.

Compared with `sl3-large-prime-collapse-from-weak-ucp-stability`, the sole
open input has been reduced from weak ucp-stability of every separating
approximation of `SL_3(Z)` to `(HMR1)` for the restrictions selected by this
one HNN presentation.

