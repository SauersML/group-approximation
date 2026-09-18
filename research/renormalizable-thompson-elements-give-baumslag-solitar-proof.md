---
rg: 2
id: renormalizable-thompson-elements-give-baumslag-solitar-proof
kind: route
title: Split the tower levels by a complete prefix code in a new coordinate and conjugate T^m x id to T x id
target: renormalizable-thompson-elements-give-baumslag-solitar
requires: []
---

**The conjugator.**
- Fix a complete prefix code `c_0, …, c_{m-1}` of `C`, e.g. `1^i 0` for `i < m-1` and
  `1^{m-1}`.
- Define `g: X × C -> X × C` by `g(T^i a, y) = (φ(a), c_i y)` for `a ∈ A`,
  `0 <= i <= m-1`, `y ∈ C`.

**It is a bijection.**
- By item 1 of the definition, every point of `X × C` is `(T^i a, y)` for unique
  `i`, `a ∈ A`, `y`.
- `g` maps the level `T^i A × C` onto `X × C(c_i)` by `(φ ∘ T^{-i}) × (c_i ·)`.
- The cones `C(c_i)` partition `C`, and `φ` is a bijection.

**It lies in `(k+1)V`.**
- On `T^i A`, the map `φ ∘ T^{-i}` is a composite of `T^{-i} ∈ kV` with the brick-local
  `φ`. Composites of brick-wise prefix replacements are prefix replacements on a finer
  finite brick partition, as for products in `kV`.
- So on each brick `B` of that partition, `g(B × C) = B' × C(c_i)` is a prefix
  replacement in all `k + 1` coordinates. In the last coordinate it is `ε ↦ c_i`.
- The image bricks partition `X × C` because `g` is a bijection. So `g ∈ (k+1)V`.

**It conjugates.** Let `s = T × id`. For `a ∈ A`, `0 <= i <= m-1` and `y ∈ C`:
- `s^m (T^i a, y) = (T^i (T^m a), y)`, and `T^m a ∈ A` by item 1.
- So `g(s^m (T^i a, y)) = (φ(T^m a), c_i y) = (T φ(a), c_i y) = s(g(T^i a, y))`, using
  item 2.
- Hence `g s^m = s g`, that is `g^-1 s g = s^m`. Put `u = g^-1`, so `u s u^-1 = s^m`.

**The subgroup is `BS(1,m)`.** `s` has infinite order because `T` does. Write
`BS(1,m) = ⟨σ, υ | υ σ υ^-1 = σ^m⟩ = Z[1/m] ⋊ Z`, with `σ = 1 ∈ Z[1/m]` and `υ`
acting by multiplication by `m`. The surjection `σ ↦ s`, `υ ↦ u` has kernel `N`, a
normal subgroup.
- If `N ∩ Z[1/m] ≠ 0`, this intersection is a nonzero subgroup invariant under
  multiplication by `m^{±1}`. So it contains a nonzero integer `j`, and `s^j = 1`,
  which is impossible.
- If `N ∩ Z[1/m] = 0`, then `N` embeds in the quotient `Z`, and
  `[N, Z[1/m]] ⊆ N ∩ Z[1/m] = 0`. An element `(b, υ^e)` centralizing `Z[1/m]` has
  `m^e = 1`, so `e = 0`. Then `N ⊆ Z[1/m]`, so `N = 0`.

So `⟨s, u⟩ ≅ BS(1,m)`. This is the hand check of `bs12-embeds-in-brin-thompson-2v`
for general `m`. ∎

**Remark.** The odometer model is the case `k = 1`, `m = 2`, `A = C(0)`,
`φ(0w) = w`, code `{0, 1}`. There `g(x_0 w, y) = (w, x_0 y)`, which is the baker map
`b` itself, and `g^-1 s g = s^2` is the formula `b^-1 (τ × id) b = τ^2 × id` of
Attempt 1 in `bs12-embeds-in-brin-thompson-2v`.
