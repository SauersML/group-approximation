---
rg: 2
id: fg-restricted-product-actions-have-finite-support-proof
kind: route
title: Direct proof via the support cocycle D(gh) in D(g) union sigma_g(D(h))
target: fg-restricted-product-actions-have-finite-support
requires:
  - sl-2-q-root-group-is-parabolic-in-every-prime-factor
  - adelic-median-graph-automorphisms-are-restricted-products
---

Direct proof. Not independently reviewed. The required node supplies the fact that
`u(1/p)` moves `o_p`; the required automorphism node supplies the fact that
`Aut(∏'_p T_p)` acts coordinatewise.

## Step 1. The support cocycle

Let `g, h` be monomial and `j ∈ I`, and put `i = σ_g^-1(j)`. Then
`(g h o)_j = g_i((h o)_i)`. If `i ∉ D(h)`, then `(h o)_i = o_i`, and
`g_i(o_i) = (g o)_j`, which equals `o_j` unless `j ∈ D(g)`. Hence

    D(g h) ⊆ D(g) ∪ σ_g(D(h)).

Also `D(h^-1) = σ_h^-1(D(h))`, because `(h^-1 o)_i ≠ o_i` iff `o_(σ_h(i)) ≠ (h o)_(σ_h(i))`.

## Step 2. Parts 1 and 2

Write `h = f_1 ... f_l` with `f_k ∈ F^(±1)` and `l = |h|_F`. By induction on `l`,
Step 1 gives `D(h) ⊆ ⋃_k σ_(f_1...f_(k-1))(D(f_k))`. Each term has size
`|D(f_k)| <= s`, by the formula for `D(f^-1)`, and is contained in `σ(H) · S`.
This is part 1.

If every `σ_f` is the identity, then `D(h) ⊆ S`. So for `i ∉ S`, `h_i(o_i) = o_i`
for all `h ∈ H`, and `h` maps `Ω_S` into itself. If each `Ω_i` is the vertex set of
a connected graph and `H` acts by graph automorphisms, then `Ω_S` is the set of
vertices whose coordinates outside `S` are base points. This set is convex for the
sum-of-distances metric, since a geodesic changes only coordinates in which its
endpoints differ. That gives part 2.

## Step 3. Part 3

Let `G = ∏'_i (G_i, K_i)` act on `∏'_i (G_i/K_i, K_i)` by left multiplication in each
coordinate. This action is coordinatewise, with `D(g) = {i : g_i ∉ K_i}`. By part 2,
a finitely generated subgroup has `g_i ∈ K_i` for all `i ∉ S`.

## Step 4. Consequences

- **Moving the base points.** In the building of `SL_n(Q_p)` or `PGL_n(Q_p)`, the
  element `x_12(1/p)` does not stabilize `Z_p^n` up to homothety: it maps `e_2` to
  `e_2 + e_1/p`. So it moves `o_p`. For `Aff(Q)`, embed `x -> ax + b` as
  `[[a, b], [0, 1]]` in `PGL_2(Q)`. Then `x -> x + 1/p` is `u(1/p)`, which moves
  `o_p` (`sl-2-q-root-group-is-parabolic-in-every-prime-factor`, Part 2). If a
  finitely generated coordinatewise `H` contained these elements acting in this
  way, part 2 would give `o_p` fixed for all `p ∉ S`, a contradiction.
- **Automorphisms of `X = ∏'_p T_p`** are coordinatewise by item 1 of
  `adelic-median-graph-automorphisms-are-restricted-products`.
- **Monomial bound.** For `h = u(1/m!)`, `D(h) ⊇ {p <= m}`, so part 1 gives
  `π(m) <= s |h|_F`.
