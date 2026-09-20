---
rg: 2
id: finite-planar-non-wedge-from-periodic-rips-h2-torsion
kind: route
title: "A periodic planar pattern with torsion in Rips H_2 over the translation bends to finite planar sets whose Rips complexes are not wedges of spheres"
target: some-finite-planar-set-has-a-non-wedge-rips-complex
requires: [some-periodic-planar-pattern-has-rips-h2-torsion, periodic-planar-rips-patterns-bend-to-finite-quotients, wedges-of-spheres-have-free-cyclic-cover-homology]
---

Take `M, v, r, Y` and a field `k` as in
`some-periodic-planar-pattern-has-rips-h2-torsion`, with `R_r(Y)` connected.
Take `0 ≠ z ∈ H_2(R_r(Y); k)` and `0 ≠ p ∈ k[t^{±1}]` with `p(t) z = 0`,
where `t = τ_*`.

**Step 1 (bend).** By `periodic-planar-rips-patterns-bend-to-finite-quotients`
there is an `N` for which the following hold:
- `X_N ⊆ R^2` is finite;
- `R_r(X_N)` is connected;
- the quotient `R_r(Y) → R_r(X_N)` is a connected infinite cyclic covering
  with deck generator `τ^N`.

On `H_2(R_r(Y); k)` this generator acts as `s = t^N`.

**Step 2 (torsion survives over `k[s^{±1}]`).** Multiply `p` by a unit so that
it is a polynomial of degree `d` with nonzero constant term. The span
`W = span_k{z, tz, …, t^{d−1} z}` is finite-dimensional. It is stable under
`t`, and also under `t^{−1}`, because `p` has nonzero constant term. So `s`
acts on `W`, and its minimal polynomial `q ≠ 0` gives `q(s) z = 0`. Hence
`z` is a nonzero torsion element of `H_2(R_r(Y); k)` as a
`k[s^{±1}]`-module.

**Step 3 (certificate).** Suppose `R_r(X_N)` were homotopy equivalent to a
wedge of spheres. `wedges-of-spheres-have-free-cyclic-cover-homology`, part
1, states verbatim: "Let `T` be a connected CW complex homotopy equivalent to
a wedge of spheres `∨_{i∈I} S^{n_i}` (all `n_i ≥ 1`), let `T̃ → T` be a
connected infinite cyclic covering with deck generator `t`, and let `k` be a
field. Then: 1. `H_q(T̃; k)` is a free `k[t^{±1}]`-module for every
`q ≥ 1`". Apply it with `T = R_r(X_N)`, `T̃ = R_r(Y)` and deck generator
`s`. Then `H_2(R_r(Y); k)` is a free `k[s^{±1}]`-module. Free modules over a
domain are torsion-free, which contradicts Step 2. Therefore the finite
planar set `X_N` has a connected Rips complex `R_r(X_N)` that is not
homotopy equivalent to any wedge of spheres. ∎

**What this changes.** Attempt (B) of the target is the case where `M` is a
cluster and `v` a step around the circle. Its recorded obstacle is that
carrying a sphere needs steps below `r` while separation needs steps above
`r`. The obstacle comes from computing `H_2` of the cover by Mayer–Vietoris
over separated pieces. The route above needs no separation: any generic
pattern works, and the torsion is read off by the finite twisted computation
in the hole. The only obstacle left is survival of the carried class in
`R_r(Y)`. The Attempts of the hole record the search. In every searched
family, spheres either stay separated (free `H_2`) or the carried sphere dies
in `R_r(Y)`. Cone points are the suspected mechanism.
