---
rg: 2
id: congruence-regular-padding-conductor-proof
kind: route
title: Dominate a semigroup conductor by the regular cell vector and test the Weil line
target: congruence-regular-padding-is-conductor-not-low-rank
requires:
  - three-way-cell-semigroups-have-conductor-but-unbounded-charge
  - bs14-native-cell-padding-preserves-lattice-charge
  - bs14-native-cells-cross-every-length-cutoff
  - congruence-induction-cannot-reconstruct-a-low-rank-bs14-boundary
---

Lift the fixed conductor to `z_E in N^E`.  Positivity of the regular cell
vector lets a multiple dominate this lift coordinatewise, proving `(CRP1)`.
Equation `(CRP2)` is immediate because every regular margin lies in the
same restriction lattice.

For the quantitative obstruction, delete the unique trivial BS line from
the full even-Weil endpoint.  Adding `Reg(Q_p)` restores integrality by
removing its trivial global summand as in `(CRP4)`.  The exact orders in
`(CRP3)--(CRP5)` show that the padding-to-core dimension ratio is
`p(p+1)`, despite active rank one.  The nonzero packets have period
`ord_p(4)`, which is unbounded, so the same family proves the short-source
cutoff assertion.
