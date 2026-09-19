---
rg: 2
id: brick-groupoid-has-no-principal-cantor-factor-proof
kind: route
title: "Compute the isotropy of G_2^n coordinatewise, note that isomorphisms carry isotropy groups to isotropy groups and top strata to top strata, and compare cardinalities"
target: brick-groupoid-has-no-principal-cantor-factor
requires: []
---

Notation is that of the target claim.

## Step 1. Isotropy of G_2

Let `x ∈ C`. An isotropy arrow at `x` is `(x, m, x)` with `m = k − l` and `σ^k x = σ^l x`.

- If `x ∉ E` and `σ^k x = σ^l x` with `k ≠ l`, say `k > l`, then `y = σ^l x` satisfies
  `σ^{k−l} y = y`. So `y` is periodic and `x` is eventually periodic, which is a
  contradiction. Hence `m = 0`, and the isotropy group is trivial.
- If `x ∈ E`, let `q ≥ 1` be the least period of the periodic tail and `t` the
  preperiod. Then `σ^{t+q} x = σ^t x`, so `(x, q, x)` is an isotropy arrow.
- The map `(x, m, x) ↦ m` is an injective homomorphism of the isotropy group into `Z`.
  - Homomorphism: `(x, m, x)(x, m', x) = (x, m + m', x)`.
  - Injective: the arrow is determined by `m`.
- So the isotropy group is a nonzero subgroup of `Z`, hence `≅ Z`.

## Step 2. Isotropy of products

In a product groupoid `𝒜 × ℬ`, arrows are pairs, and `r`, `s` and multiplication are
coordinatewise. So `(𝒜 × ℬ)_{(a,b)}^{(a,b)} = 𝒜_a^a × ℬ_b^b`.

Applied to `G_2^n` with Step 1, the isotropy at `x` is `≅ Z^{p(x)}`. The rank `n` is attained
exactly on `E^n`. `E` is countable, because an eventually periodic sequence is determined by
two finite words. So `E^n` is countable. It is dense, because every cylinder contains an
eventually periodic point. This proves (a).

Reductions: for a set of units `U`, the reduction `𝒢|_U = {g : r(g), s(g) ∈ U}` has the same
isotropy groups at points of `U`.

## Step 3. Isomorphisms preserve isotropy

Let `φ : 𝒢 → ℋ` be a groupoid isomorphism.

- `φ` maps units to units, since units are the arrows `e` with `ee = e`, and these are
  preserved.
- `φ` restricts to a bijection `𝒢^{(0)} → ℋ^{(0)}` with `φ(r(g)) = r(φ(g))`, since
  `r(g) = gg^{-1}`.
- So `φ` maps `𝒢_u^u` isomorphically onto `ℋ_{φ(u)}^{φ(u)}`.

## Step 4. Proof of (b)

Let `φ : 𝒫 × 𝒦 → G_2^n|_U` be an isomorphism, and let `(a,b)` be a unit.

- By Steps 2 and 3, `𝒫_a^a × 𝒦_b^b ≅ Z^{p(φ(a,b))}`.
- Each factor embeds as a subgroup of `Z^{p}` with `p ≤ n`. So it is free abelian of rank
  `≤ n`, and `rk(a) + rk(b) = p(φ(a,b))`.

Let `R_𝒫` and `R_𝒦` be the maxima of `rk` on `𝒫^{(0)}` and `𝒦^{(0)}`. They exist because
ranks are bounded by `n`.

- `max (rk(a) + rk(b)) = R_𝒫 + R_𝒦`, since the unit space is a full product.
- `φ` is a bijection onto `U`, and `U ∩ E^n ≠ ∅` means the maximum of `p` on `U` is `n`.
- So `R_𝒫 + R_𝒦 = n`, and
  `φ^{-1}(U ∩ E^n) = {(a,b) : rk a + rk b = n} = S_𝒫 × S_𝒦`.
- Its image `U ∩ E^n` is countable, so `S_𝒫 × S_𝒦` is countable.
- Both factors are nonempty, since the maxima are attained. So `S_𝒫` and `S_𝒦` are
  countable. This proves (b).

## Step 5. The corollaries

**(c).1.** Let `𝒫` be principal. Then `rk ≡ 0` on `𝒫^{(0)}`, so `S_𝒫 = 𝒫^{(0)}`, which is
uncountable. This contradicts Step 4.

**(c).2.** Let `Γ ↷ M` be free. In the transformation groupoid `M ⋊ Γ`, the isotropy at `m`
is `{(m, γ) : γm = m} ≅ Γ_m`, which is trivial. So `M ⋊ Γ` is principal. `M` is a Cantor
set, hence uncountable. Apply (c).1 with `𝒦 = G_2`.

**(c).3.** Let `U ⊆ C^n` and `V ⊆ M × C` be nonempty open, and suppose
`φ : 𝒢_W1|_V → G_2^n|_U` is an isomorphism. Here the unit set of the product is
`M × C`, and the rank at `(m, y)` is `0 + rk_{G_2}(y) ≤ 1`.

- `U ∩ E^n` is nonempty and countable, since `E^n` is dense and `U` is open. So the maximal
  rank on `U` is `n`.
- The maximal rank on `V` is at most `1`. So `n = 1`, and the rank-1 set of `V` is
  `V ∩ (M × E)`.
- `V` contains a basic open set `A × [w]`, with `A ⊆ M` nonempty open and `[w]` a
  cylinder. `[w]` contains a point `e ∈ E`, so `V ∩ (M × E) ⊇ A × {e}`.
- `A` is uncountable, because a nonempty open subset of a Cantor set is uncountable. So
  the rank-1 set of `V` is uncountable.
- The rank-1 set of `U` is `U ∩ E`, which is countable. `φ` maps one onto the other, which
  is a contradiction.

**(c).4.** Take `𝒫 = Γ ⋉ Ω`, whose isotropy at `ω` is `Γ_ω`, and `𝒦 = G_2`, whose rank
maximum is `1` and whose `S_𝒦 = E`. By Step 4:

- each `Γ_ω` is free abelian of rank `≤ n`;
- `R_𝒫 = n − 1`;
- `S_𝒫 = {ω : rk Γ_ω = n − 1}` is countable and nonempty.

If `Γ ↷ Ω` were free, then `R_𝒫 = 0` and `S_𝒫 = Ω`, which is uncountable. So the action is not
free, and `n − 1 = R_𝒫 ≥ 1`.

## Remark (standard facts, not part of the established statement)

For a lattice `Γ` acting on the Bruhat–Tits building `B` of `PGL_3(K)`, freely on vertices:

- A torsion-free subgroup `H` acts freely on `B`. An element fixing a point stabilizes the
  carrier simplex, so a power of it fixes a vertex, and that power is trivial.
- Since `B` is contractible and 2-dimensional, `B/H` is a 2-dimensional `K(H,1)`, and
  `cd H ≤ 2`.
- `cd Z^j = j`. So every free abelian `Γ_ω` has rank `≤ 2`, and (c).4 leaves only
  `n ∈ {2, 3}`.

This rests on standard textbook facts: buildings are CAT(0), hence contractible, and
`cd Z^j = j`. No verbatim citation is included, so it is recorded as a remark.
