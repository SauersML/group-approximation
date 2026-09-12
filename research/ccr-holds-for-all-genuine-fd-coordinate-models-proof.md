---
rg: 2
id: ccr-holds-for-all-genuine-fd-coordinate-models-proof
kind: route
title: Equal finite dimension upgrades the automatic containment to equality, then Kazhdan lands the ultraproduct
target: ccr-holds-for-all-genuine-fd-coordinate-models
requires: []
artifacts:
  - research/artifacts/fd-compressor-commutant-and-cycle-rounding-2026-09-12.md
---

# Theorem A: the dimension count

Let `pi : G -> U(D)` be finite-dimensional, `Lambda = t Gamma t^-1` inside
`Gamma`.

1. `Lambda` is contained in `Gamma`, so `pi(Lambda)` is contained in `pi(Gamma)`,
   and commutants reverse inclusions: `pi(Gamma)'` is contained in `pi(Lambda)'`.
2. `pi(Lambda) = pi(t) pi(Gamma) pi(t)*`, hence
   `pi(Lambda)' = pi(t) pi(Gamma)' pi(t)*`. Conjugation by a unitary is a linear
   bijection of `M_D`, so `dim_C pi(Lambda)' = dim_C pi(Gamma)'`.
3. A containment of linear subspaces of `M_D` of equal finite dimension is an
   equality. So `pi(Lambda)' = pi(Gamma)'`, and by step 2
   `Ad pi(t)(pi(Gamma)') = pi(Gamma)'`. QED

# Corollary A1: the ultraproduct

`Lambda <= Gamma` gives `sigma(Gamma)' ∩ M` inside `sigma(Lambda)' ∩ M`. For the
converse take `x = (x_n)` in `sigma(Lambda)' ∩ M` with `||x|| <= 1`. Fix a finite
generating set `S` of `Lambda` with Kazhdan constant `kappa > 0`, so that for
every unitary representation `rho` of `Lambda` on a Hilbert space `V` and every
`v` in `V`,

```text
max_(s in S) ||rho(s)v - v|| >= kappa · dist(v, V^(rho(Lambda))).      (K)
```

1. `[x, sigma(s)] = 0` for the finitely many `s` in `S` means
   `eps_n := max_(s in S) ||x_n - pi_n(s) x_n pi_n(s)*||_2 -> 0` along `U`.
2. Apply (K) to the conjugation representation `Ad(pi_n|_Lambda)` of `Lambda` on
   `(M_(d_n), ||·||_2)` and the vector `x_n`. Its fixed-point space is
   `pi_n(Lambda)'`, so `dist_2(x_n, pi_n(Lambda)') <= eps_n / kappa -> 0`.
3. By Theorem A, `pi_n(Lambda)' = pi_n(Gamma)'` for every `n`. This is the step
   where `ccr-for-coordinate-collapsing-models-proof` needed image collapse and
   uniformity in `lambda`; neither is used here.
4. Let `y_n = E_n(x_n)` with `E_n` the `tr`-preserving conditional expectation of
   `M_(d_n)` onto the von Neumann subalgebra `pi_n(Gamma)'`, i.e. averaging over
   `pi_n(Gamma)`. `E_n` is the `||·||_2`-orthogonal projection onto
   `pi_n(Gamma)'` and is an operator-norm contraction, so `||y_n|| <= 1` and
   `||x_n - y_n||_2 = dist_2(x_n, pi_n(Gamma)') -> 0`.
5. Hence `y = (y_n)` is an element of `M`, `x = y`, and `y` lies in
   `prod_U pi_n(Gamma)'`, which is contained in `sigma(Gamma)' ∩ M`. QED

# Why this does not close the parent question

Steps 1, 2, 4 and 5 survive for an arbitrary `sigma`. Step 3 does not: for
approximate coordinate maps there is no representation `pi_n` of `G`, so
`pi_n(Lambda)` is not a unitary conjugate of `pi_n(Gamma)` and the dimension
count has nothing to compare. That is the same wall as Alekseev--Thom Open
Problem 6.2, recorded on `kt-centralizer-normalization-hs`.
