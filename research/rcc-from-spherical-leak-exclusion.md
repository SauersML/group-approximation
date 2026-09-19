---
rg: 2
id: rcc-from-spherical-leak-exclusion
kind: route
title: The far-defect formula plus leak exclusion give the relative commutant collapse
target: relative-commutant-collapse-for-sl2-pair
requires:
  - hecke-far-commutator-defect-formula
  - no-spherical-leak-in-matrix-ultraproducts
---

Fix a tracial matrix ultraproduct `M` and a trace-preserving
regular-trace representation `pi` of `Gamma = SL_2(Z[1/2])`, with
`Lambda = SL_2(Z)`.  The inclusion `pi(Gamma)' cap M subseteq
pi(Lambda)' cap M` is trivial; `(RCC)` is the reverse inclusion.

Let `k` be any unitary of `pi(Lambda)' cap M`.  By
`no-spherical-leak-in-matrix-ultraproducts`,
`|| E_(pi(Gamma)' cap M)(k) ||_2 = 1`; since `k` is a unit vector of
`L^2(M)` and `E` is an orthogonal projection there, `E(k) = k`, so
`k in pi(Gamma)' cap M`.  A von Neumann algebra is the norm-closed
linear span of its unitary group, so
`pi(Lambda)' cap M subseteq pi(Gamma)' cap M`, which is `(RCC)`.

The role of `hecke-far-commutator-defect-formula` is to make the leak
statement meaningful and checkable: it identifies the deficiency
`1 - ||E(k)||_2^2` with the asymptotic far-coset commutator defect and
with the mass of a `c_0` spherical component on `PSL_2(Q_2)`, so the
exclusion claim quantifies over one scalar per element rather than over
subalgebra inclusions.  The same two inputs, read for `n >= 3`, prove
the corresponding collapse for the `SL_3` pair, where the exclusion
claim additionally has the property (T) Hecke contraction recorded in
its attempts.
