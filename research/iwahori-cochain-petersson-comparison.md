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
- (i) and (iii): proposed uniform argument (2026-08-21), not yet written
  out.  Work on the fixed orbifold `X(1)` with the flat unitary bundle
  `E_rho` of rank `d^2`.  *Upper bound* `||omega||_(L^2) <= C ||c||`: the
  harmonic representative minimizes the `L^2` norm in its class (Hodge),
  and a closed form with the prescribed periods is built from the cocycle
  values by a fixed scalar cutoff interpolation on the fundamental domain,
  so its energy is at most a fixed constant times the cochain norm,
  independently of `d`.  *Lower bound* `||[c]||_(quot) <= C ||omega||_(L^2)`:
  the cocycle on the generators is given by integrals of `omega` along
  fixed paths inside the compact core (`2i -> 2i+1` for `u`, `2i -> i/2` for
  `S`), and interior elliptic estimates for harmonic sections of a flat
  unitary bundle are componentwise scalar, hence uniform in the rank.
  *Eisenstein part*: in the `Ad rho`-on-`SL_2(Z)` formulation the boundary
  of a class is its image in the `u`-coinvariants `M_d / (1 - Ad rho(u))
  M_d`, a generator-level quantity; by Shapiro this is the cusp residue
  vector of `Gamma(p)` with orbit-size weights, all equal to `p` except at
  finitely many cusps, so the Gram identity of `iwahori-eisenstein-angle`
  transfers with the same interval up to a bounded correction.
  *Coboundaries*: Selberg's `(tau)`.  The orthogonality of the three parts
  in the cochain inner product is the remaining bookkeeping.
