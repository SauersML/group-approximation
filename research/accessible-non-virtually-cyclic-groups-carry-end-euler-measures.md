---
rg: 2
id: accessible-non-virtually-cyclic-groups-carry-end-euler-measures
kind: claim
title: An infinite accessible group that is not virtually cyclic carries a right-invariant finitely additive measure on its end compactification giving every point mass one
distinct_from:
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that is a counting argument on the unique infinite component of a one-ended group; this is an invariant on the whole clopen algebra of the Freudenthal compactification, defined for every accessible group with any number of ends, and it fails exactly for the two-ended groups.
  regular-enumeration-displacement-bounds-growth: that bounds growth through bounded displacement of the enumeration; the measure here is a finitely additive invariant and is insensitive to the enumeration.
artifacts:
  - experiments/window-zero-enumerations-2026-09-17/end_measure_check.py
---

**ESTABLISHED** (direct proof; not independently reviewed; no novelty
claimed; standard facts used are named in the route).

Let `P` be an infinite finitely generated group with finite generating set
`S`, and let `Gamma` be the Cayley graph with edges `{y, gy}` for `g` in `S`.
Right multiplications are graph automorphisms of `Gamma`. Write
`Pbar = P ∪ ∂P` for the Freudenthal (end) compactification. Its clopen
subsets are exactly the closures of the subsets `U` of `P` with finite
coboundary in `Gamma`, together with the finite subsets of `P`.

An **end Euler measure** is a map `mu` from the clopen subsets of `Pbar` to
`Q` that is

- finitely additive,
- invariant under every right multiplication `y -> yd`, and
- equal to 1 on every singleton `{y}` with `y` in `P`.

**Theorem.** Suppose `P` is accessible, meaning it is the fundamental group
of a finite graph of groups with finite edge groups and vertex groups having
at most one end. This includes every finitely presented group (Dunwoody).
If `P` is not virtually cyclic, then `P` carries an end Euler measure.

- If `P` has one end, any value `T = mu(Pbar)` works:
  `mu(finite F) = |F|` and `mu(Pbar minus F) = T - |F|`.
- If `P` has infinitely many ends and some vertex group is infinite, again
  any `T` works.
- If every vertex group is finite (`P` virtually free), the measure exists,
  and every end Euler measure has `mu(Pbar) = 1/chi(P)`, where `chi` is the
  rational Euler characteristic.

The hypothesis cannot be dropped. For `P = Z`, finite additivity and
invariance of `[r, +infinity]` give
`mu([r, +infinity]) = 1 + mu([r+1, +infinity]) = 1 + mu([r, +infinity])`, so
no measure exists. The linear system of the route is also inconsistent for
`D_inf`, `Z x Z/2` and `Z/4 *_(Z/2) Z/4`, as checked by the script.

Example: `P = F_2` has `mu(Pbar) = -1 = 1/chi(F_2)`.

Groups that are finitely generated but inaccessible are not treated.

DERIVATION
accessible-end-euler-measure-proof
