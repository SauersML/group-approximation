---
rg: 2
id: iwahori-eisenstein-angle
kind: claim
title: The two Iwahori restriction maps are uniformly transverse on Eisenstein cohomology
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-cuspidal-hecke-angle: that handles square-integrable classes through Deligne; this handles the boundary (Eisenstein) classes, whose Hecke eigenvalue at 2 is the degenerate value 3 and whose harmonic representatives are not square-integrable, so a separate finite computation is needed.
---

With notation as in `iwahori-cuspidal-hecke-angle`, let `H^1_Eis` denote the
Eisenstein (boundary) part of `H^1(Gamma(p), Ad rho)`, identified with
functions on the cusps of `X(p)` modulo constants, equivariantly for
`SL_2(F_p)`.  **Claim:** there is `c > 0`, independent of `p` and `rho`,
such that for Eisenstein classes `f, g` (measured in a natural cusp-count
norm) `|| res_1 f - res_2 g || >= c (||f|| + ||g||)` modulo the image of
the diagonal coboundaries, i.e. the restriction of the Mayer--Vietoris
mismatch map to Eisenstein cohomology is uniformly injective.

Injectivity itself holds because `H^1(SL_2(Z[1/2]), Ad rho) = 0`
(property (T;FD)); the content is the uniform constant.

## Attempts

- **Naive Hecke heuristic fails.**  On Eisenstein classes `T_2` has
  eigenvalue `3`, which in the cuspidal identity would give zero; the
  identity does not apply because Eisenstein harmonic forms are not
  square-integrable, so `res_1^* res_2 = T_2` is not valid in the cochain
  inner product.  The Eisenstein part must be computed directly.
- **Combinatorial model.**  Cusps of `Gamma(p)` are `+-`-classes of
  primitive vectors in `(Z/p)^2`; cusps of `B(p)` are their `Gamma^0(2)`-
  refinement; the two restrictions are the two natural maps between the
  cusp sets induced by the identity and by `t`.  The mismatch map on
  Eisenstein cohomology is therefore an explicit finite incidence
  operator between cusp sets, and its singular values can be computed
  as functions of `p` (a finite-dimensional problem of size about `p^2`).
  A uniform lower bound on its smallest nonzero singular value is the
  claim.
- **Numerics.**  The full-cochain singular values in
  `experiments/iwahori_linearized_gap.py` mix both parts; a cusp-only
  computation would isolate this one.
