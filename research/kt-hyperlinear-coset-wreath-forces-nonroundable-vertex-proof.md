---
rg: 2
id: kt-hyperlinear-coset-wreath-forces-nonroundable-vertex-proof
kind: route
title: Extract the actor model from the wreath, find a moved lamp off the core, and run the unit-type rounding chain
target: kt-hyperlinear-coset-wreath-forces-nonroundable-vertex
requires:
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - nonunit-projection-bounded-by-root-spectral-mass
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - vertex-rounding-deep-nonunit-root-mass-vanishes
  - kt-wreath-hyperlinear-iff-double-hyperlinear
---

**Step 1 (the model).** A countable hyperlinear group admits a trace-preserving embedding
into the unitary group of a tracial matrix ultraproduct: add a trivial summand and take
tensor powers along the ultrafilter, as in Section 1 of
`research/artifacts/rigid-compression-defect-ladder-2026-09-11.md`. Let `theta` be such an
embedding of `W_K`, and put `sigma = theta|G`, which is trace-preserving.

**Step 2 (a moved lamp).** Write `a_x = theta(e_x)` for the lamp at the coset `x in G/K`.
- `K` fixes the coset `K`, so `a_K` commutes with `theta(K)`, which contains `sigma(Gamma)`.
  Hence `a_K in R`.
- If `Gamma` were contained in `g K g^(-1)` for every `g in G`, it would lie in
  `core_G(K)`, which is normal and contained in `K`, so `N <= K`. That is excluded, so
  there are `g in G` and `gamma in Gamma` with `gamma notin g K g^(-1)`, i.e.
  `gamma g K != g K`.
- Then `sigma(g) a_K sigma(g)^* = a_(gK)`, and
  `sigma(gamma) a_(gK) sigma(gamma)^* = a_(gamma g K)`, a different lamp. The product
  `e_(gK) e_(gamma g K)` is a nontrivial element of `W_K`, so its canonical trace is `0`,
  and `||a_(gamma g K) - a_(gK)||_2 = sqrt 2`.
- So `a_(gK)` does not commute with `sigma(gamma)`, and `sigma(G)` does not normalize `R`.
  This is item 1.

**Step 3 (rounding would normalize).** Suppose (H1) holds at `sigma` with roundings `pi_n`.
All four premises are statements about one trace-preserving model with (H1) roundings, for
the explicit Theorem E pair with `r, d >= 3`.
- Item 1 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`: each `pi_n`
  factors through `St_r(R_+/I_n)` with `R_+/I_n = A_u x A_nu`, and `P_n` is defined.
- `nonunit-projection-bounded-by-root-spectral-mass`:
  `tau(1 - P_n) <= r(r-1)[mu_n(depth_nu = 1) + mu_n(depth_nu > 1)]`.
- Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding`:
  `mu_n(depth_nu = 1) -> 0`.
- `vertex-rounding-deep-nonunit-root-mass-vanishes`: `mu_n(depth_nu > 1) -> 0`.
- So `tau(1 - P_n) -> 0` along `U`. Item 4 of the first premise then gives that `sigma(G)`
  normalizes `R`, contradicting Step 2. Hence (H1) fails at `sigma`, which is item 2.

**Step 4 (stability and the double).** Flexible normalized-HS stability of `Gamma` would give
(H1) at every asymptotic representation of `Gamma`, including `sigma|Gamma`, so `Gamma` is not
flexibly stable. If `G *_Gamma G` is hyperlinear, `kt-wreath-hyperlinear-iff-double-hyperlinear`
makes `W_Gamma` hyperlinear. `K = Gamma` qualifies, because `Gamma` is not normal in `G`.
