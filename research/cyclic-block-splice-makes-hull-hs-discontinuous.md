---
rg: 2
id: cyclic-block-splice-makes-hull-hs-discontinuous
kind: route
title: Splice two permutation cycles in two coordinates and compare bounded word neighborhoods
target: finite-word-data-cannot-authenticate-canonical-cyclic-hull
requires:
  - canonical-reached-hulls-tensor-amplify-fully
---

Take the interval projection `p_d`, the full cycle `u_d`, and the two block
cycles `v_d` from `(FCH1)--(FCH3)`.  Direct calculation on the two altered
columns gives `(FCH2)`.  Translation by the full cycle makes the reducing hull
of the interval all of `C^d`; the two block cycles leave it equal to the
interval.

Multiplication by `B_d` changes signs but never support, and each occurrence
of `u_d` or `u_d^*` moves support by one coordinate.  A word of radius `L`
therefore stays inside the `L`-neighborhood, proving `(FCH4)`.  Finally,
telescoping a fixed word product bounds its normalized-HS change by its number
of moving-letter occurrences times `(FCH2)`.  Finite sums, relator defects,
and normalized moments inherit the same `o(1)` bound.
