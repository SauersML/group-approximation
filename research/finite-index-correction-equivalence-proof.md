---
rg: 2
id: finite-index-correction-equivalence-proof
kind: route
title: Combine word restriction with induced-projection correction
target: finite-index-correction-is-equivalent-for-kazhdan-groups
requires:
  - subgroup-exact-outliers-do-not-exist
---

An exact ambient representation restricts to an exact subgroup
representation.  Evaluating the finitely many subgroup generators as fixed
ambient words and telescoping shows that a flexible ambient correction
restricts to a flexible `N`-correction.

Conversely, stabilize a flexible exact `N`-correction and the original
restriction to a common dimension.  Delete their `o(d)` unmatched corners;
on the remainder the subgroup tuple is near an exact representation, while
filling the deleted corner arbitrarily changes every normalized-HS defect by
`o(1)`.  Apply `subgroup-exact-outliers-do-not-exist`: induction of the exact
`N`-representation, property `(T)` for the exact induced conjugation action,
and rounding its almost-invariant range projection produce a flexible exact
`G`-correction.  This proves the equivalence and its congruence-tower
consequence.
