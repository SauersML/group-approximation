---
rg: 2
id: iwahori-cochain-petersson-comparison
kind: claim
title: Cochain Hilbert--Schmidt norms and harmonic norms on Iwahori cocycle spaces are uniformly comparable modulo coboundaries
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that is the target inequality; this is the bookkeeping step that transfers a cohomological angle bound into the cochain norm used by the stability question.
---

Let `rho` be a congruence representation of `SL_2(Z[1/2])` and `V` one of
`SL_2(Z)`, `SL_2(Z)^t`, `Gamma^0(2)`.  On `Z^1(V, Ad rho)` use the cochain
norm `max_s ||c(s)||_2` over a fixed generating set.  **Claim:** there are
constants, independent of `rho` and of the dimension, such that (i) every
cocycle is within a bounded multiple of its cochain norm of a coboundary
plus a harmonic representative, (ii) on coboundaries `||delta x|| >= kappa
||x - Ex||_2` with `E` the projection onto `rho(V)'` (this is Selberg's
property `(tau)` for `V`), and (iii) on harmonic representatives the
cochain norm and the Petersson/cusp-count norm are comparable.

## Attempts

- (ii) is immediate from property `(tau)` for congruence quotients of the
  three groups, all finite-index in `SL_2(Z)`.
- (i) and (iii) are the content: for virtually free `V` the space
  `Z^1(V, Ad rho)` is finite-dimensional of dimension about `(1 + 1/12) d^2`
  (resp. `(1 + 1/4) d^2`), the harmonic representatives are given by
  Eichler--Shimura with coefficients, and the comparison constants must
  not depend on `d`.  No argument is recorded yet.
