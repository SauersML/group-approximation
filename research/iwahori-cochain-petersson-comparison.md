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
norm `max_s ||c(s)||_2` over a fixed generating set.  **ESTABLISHED:** there are
constants, independent of `rho` and of the dimension, such that (i) every
cocycle is within a bounded multiple of its cochain norm of a coboundary
plus a harmonic representative, (ii) on coboundaries `||delta x|| >= kappa
||x - Ex||_2` with `E` the projection onto `rho(V)'` (this is Selberg's
property `(tau)` for `V`), and (iii) on harmonic representatives the
cochain norm and the Petersson/cusp-count norm are comparable.

## Progress and remaining gap

- (ii) is immediate from property `(tau)` for congruence quotients of the
  three groups, all finite-index in `SL_2(Z)`.
- (i) and the compact-core cellular/harmonic comparison in (iii) are
  `fixed-complex-unitary-local-system-hodge-norms-are-uniform`: Whitney and
  smoothed de Rham chain maps on one fixed compact core have operator norms
  independent of rank and unitary holonomy.
- The only nonformal part of separating interior and boundary is
  `iwahori-parabolic-boundary-splitting-is-uniform`.  In the exact model
  `H^1(C_2*C_3,M)=ker P_(C2) cap ker P_(C3)`, the adjoint boundary map is
  `y |-> (1-a)y`; on `u`-fixed vectors its `a`- and `b`-displacements agree,
  so property `(tau)` bounds it below off the invariant kernel.
- The Iwahori edge needs only its total fixed-complex Hodge comparison.  In
  assembling the mismatch, first pass to the edge boundary quotient; the
  Eisenstein estimate controls both vertex boundary parts.  Subtract them,
  then use the cuspidal estimate on the remaining interior mismatch.  This
  triangular argument avoids assuming that restriction preserves an
  orthogonal splitting.
- The possible cusp-tail loss is bypassed, not estimated:
  `iwahori-cuspidal-cellular-hecke-angle` proves the degeneracy-map Gram
  identity and Deligne gap directly in the Bass--Serre cellular Hodge norm.
  Thus no compact-core/full-Petersson comparison enters the proof.
