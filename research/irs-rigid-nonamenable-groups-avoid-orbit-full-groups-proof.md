---
rg: 2
id: irs-rigid-nonamenable-groups-avoid-orbit-full-groups-proof
kind: route
title: Følner vectors on a free orbit-fibred space give almost invariant vectors in a multiple of the regular representation, and ergodic decomposition turns IRS rigidity into freeness
target: irs-rigid-nonamenable-groups-avoid-amenable-orbit-full-groups
requires: []
---

Write `g` for `rho(g)`. Discard a null `Lambda`-invariant set so that `Lambda` acts
freely; every `g` preserves the complement, since `g x ∈ Lambda x`. Then
`c_(gh)(y) = c_g(hy) c_h(y)` at every point.

**Item 1.**

*The representation.* `Y` is Borel and `Gamma`-invariant. Put
`Z = {(x, lambda) ∈ X × Lambda : lambda x ∈ Y}`, `m = mu × counting`, and
`g.(x, lambda) = (x, c_g(lambda x) lambda)`. As in
`kazhdan-subgroups-amenable-orbit-full-groups-rf-proof`, Step 2, this is an action
by `m`-preserving Borel bijections, and `pi(g) f = f(g^-1 . .)` is unitary on
`L^2(Z, m)`.

*Almost invariant vectors.* For a finite `K ⊆ Gamma`, let `E` be the union of the
finite ranges of `c_k`, `k ∈ K`. For finite `Q ⊆ Lambda` put
`xi_Q = 1_(Z ∩ (X × Q))`. Then `||xi_Q||^2 = |Q| mu(Y)`, and for `k ∈ K`

```text
||pi(k) xi_Q - xi_Q||^2 / ||xi_Q||^2 <= 2 sum_(e ∈ E) |eQ \ Q| / (|Q| mu(Y)),
```

by the computation of Step 3 there, which uses only finiteness of `E`. Along a
Følner sequence the right side tends to `0`.

*Freeness on `Z`.* `(x, lambda)` is fixed by `g` iff `lambda x ∈ Fix g ∩ Y`. That set
has measure `sum_lambda mu(lambda^-1 (Fix g ∩ Y)) = 0` for `g != 1`. The union `N` of
these sets over `g != 1` is null and `Gamma`-invariant, so `Gamma` acts freely on
`Z \ N`.

*A fundamental domain.* Enumerate `Lambda = {lambda_1, lambda_2, ...}`. Let `D` be
the set of `(x, lambda) ∈ Z \ N` such that `lambda = lambda_i` for the least `i` with
`lambda_i x ∈ Gamma lambda x`. Membership is Borel, because
`{kappa x ∈ Gamma lambda x} = ∪_g {g lambda x = kappa x}`. Each orbit meets `D` in
exactly one point, and freeness gives `Z \ N = ⊔_(g ∈ Gamma) g.D`. Hence

```text
L^2(Z, m) ≅ L^2(D, m) ⊗ ell^2(Gamma),     pi(g) ≅ id ⊗ lambda_Gamma(g).
```

*Conclusion.* Let `xi_n` be unit vectors with `||pi(k) xi_n - xi_n|| -> 0` for all
`k`, and put `f_n(h) = ||xi_n(., h)||_(L^2(D))`. Then `f_n` is a unit vector in
`ell^2(Gamma)` with `||lambda_Gamma(k) f_n - f_n|| <= ||pi(k) xi_n - xi_n||`, by the
reverse triangle inequality in `L^2(D)` and summation over `h`. So `lambda_Gamma`
has almost invariant vectors, and `Gamma` is amenable (Hulanicki--Reiter). ∎

**Item 2.**

*Stabilizer map.* `Stab : X -> Sub(Gamma)`, `x -> {g : gx = x}`, is Borel for the
product Borel structure on `Sub(Gamma) ⊆ 2^Gamma`, since `{x : g ∈ Stab(x)} = Fix g`.
It is equivariant: `Stab(hx) = h Stab(x) h^-1`.

*Ergodic decomposition.* `Gamma` is countable and acts by Borel automorphisms of a
standard Borel space preserving `mu`, so `mu = ∫ mu_e dP(e)` with each `mu_e` an
ergodic invariant probability measure. Each `nu_e = Stab_* mu_e` is an ergodic
invariant random subgroup, so by hypothesis it is `delta_{1}` or `delta_Gamma`.
- If `nu_e = delta_Gamma`, then `mu_e(F) = 1`.
- If `nu_e = delta_{1}`, then `mu_e`-almost every point has trivial stabilizer.

In both cases `mu_e(Fix g ∩ Y) = 0` for every `g != 1`. Integrating over `e` gives
`mu(Fix g ∩ Y) = 0` for all `g != 1`. If `mu(Y) > 0`, item 1 makes `Gamma` amenable,
contrary to hypothesis. So `mu(Y) = 0`. ∎

**Consequence.** Let `Gamma` be non-amenable with `mu(Y) > 0`. By item 1 some
`g != 1` has `mu(Fix g ∩ Y) > 0`. Since `mu(Fix g ∩ Y) = ∫ mu_e(Fix g ∩ Y) dP(e)`,
choose a component `e` with `mu_e(Fix g ∩ Y) > 0`.
- `nu_e != delta_Gamma`: the sets `F` and `Y` are invariant and partition `X`, and
  `mu_e` is ergodic with `mu_e(Y) > 0`, so `mu_e(F) = 0`.
- `nu_e != delta_{1}`: `g ∈ Stab(x)` on a set of positive `mu_e`-measure.

So `nu_e` is a nontrivial ergodic invariant random subgroup of `Gamma`. ∎
