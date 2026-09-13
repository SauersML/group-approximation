---
rg: 2
id: weighted-similarity-exponent-pumping-proof
kind: route
title: Tame elements carry an exact locally constant weighted exponent cocycle, periodic exponents vanish, and pumping a Birkhoff sum yields a contracting cone and a periodic point of positive exponent, so the sums are bounded
target: weighted-similarity-proper-power-conjugates-are-equicontinuous
requires:
  - bilipschitz-proper-power-conjugates-have-zero-periodic-exponents
---

Notation is as in the target. `W = max_e w(e)`. Fix `L_E` so that every cone of
weight `≥ L_E` that meets `E` lies in `E`; enlarge every `L_h` to be `≥ L_E`.

**Item 0 (tame implies bi-Lipschitz).**
- Finitely many cones `C(u)` with `L_h ≤ w(u) < L_h + W` cover `E`, and their
  ratios are bounded.
- Two points in different pieces have `w(x ∧ y) < L_h + W`. Their images lie in
  disjoint compact sets, so `w(hx ∧ hy)` is bounded.

**Item 1 (exact cocycle).**
- For `x ∈ E` let `δ_h(x)` be the ratio of `h` on any cone `C(u) ∋ x` with
  `w(u) ≥ L_h`. Nested cones give the same ratio because they have at least two
  points. So `δ_h` is locally constant, hence bounded.
- **Cocycle.** Choose `u` with `h(C(u)) ⊆ C(p)`, where `w(p) ≥ L_g` and `p` is a
  prefix of `hx`. This is possible by continuity. Then `gh` is a similarity on
  `C(u)` with ratio `δ_g(hx) + δ_h(x)`, so
  `δ_(gh)(x) = δ_g(hx) + δ_h(x)`.
- Put `S_m(x) = δ_(g^m)(x) = Σ_(j<m) δ_g(g^j x)`, and `B = max |δ_g|`. Also
  `δ_(g^-1)(x) = -δ_g(g^-1 x)`.

**Item 2 (periodic spectrum vanishes).**
- Let `g^p z = z`. For `y` in a heavy cone around `z`,
  `ℓ_(g^(pm))(z, y) = w(g^(pm) z ∧ g^(pm) y) - w(z ∧ y) = m δ_(g^p)(z)`.
  So both exponents of `g^p` at `z` equal `δ_(g^p)(z)`.
- By Item 0 the required claim applies. So `δ_(g^p)(z) = 0` for every periodic
  `z`.

**Item 3 (reading weight).** Let `ℓ_m(x)` be the least `w(u)` over prefixes `u`
of `x` with `C(u) ⊆ E` on which `g^m` is a similarity. Put `L = L_g`.
- **Claim.** `ℓ_(m+1)(x) ≤ max(ℓ_m(x), L - S_m(x) + W)`.
  - Take `u` with `w(u) = ℓ_m(x)`. If `w(u) < L - S_m(x)`, replace `u` by the
    shortest prefix of `x` of weight `≥ L - S_m(x)`, which has weight
    `< L - S_m(x) + W`. Call the result `u'`.
  - For distinct `y, y' ∈ C(u')`,
    `w(g^m y ∧ g^m y') = w(y ∧ y') + S_m(x) ≥ w(u') + S_m(x) ≥ L`.
  - Let `p` be the shortest prefix of `g^m x` of weight `≥ L`. Every image point
    shares a prefix of weight `≥ L` with `g^m x`, so it has prefix `p`. Thus
    `g^m(C(u')) ⊆ C(p) ⊆ E`, `g` is a similarity on `C(p)`, and `g^(m+1)` is a
    similarity on `C(u')`.
- **Induction.** `ℓ_0(x) ≤ L_E + W`, so
  `ℓ_m(x) ≤ max(L_E + W, max_(j<m)(L + W - S_j(x)))`.

**Item 4 (pumping).** Suppose `sup_(x, m≥0) S_m(x) = +∞`. We show `g` has a
periodic point `z` with `δ_(g^p)(z) > 0`, contradicting Item 2.
- **Prefixes.** Put `A = max(L_E, L) + W`. Let `𝒫` be the finite set of shortest
  prefixes of weight `≥ A` of points of `E`, and `P = |𝒫|`.
- **Orbit and levels.**
  - Choose `x, M` with `S_M(x) - min_(k≤M) S_k(x) > (B + 1)(P + 1)`.
  - Put `h_i = min_(k≤M) S_k(x) + i(B + 1)` for `i = 0, …, P`. All are
    `< S_M(x)`.
  - Let `τ_i` be the last `k ≤ M` with `S_k(x) ≤ h_i`. Then `τ_i < M`,
    `S_k(x) > h_i` for `k > τ_i`, `S_(τ_i)(x) > h_i - B`, and `τ_i` is
    non-decreasing.
- **Pigeonhole.** Some `i < i'` give points `y = g^(τ_i) x` and
  `y' = g^(τ_(i')) x` with the same prefix `q ∈ 𝒫`.
- **Increments.**
  - `Δ = S_(τ_(i'))(x) - S_(τ_i)(x) > (h_(i') - B) - h_i ≥ 1`.
  - So `D = τ_(i') - τ_i ≥ 1`, and `y' = g^D y`.
  - For `1 ≤ j ≤ M - τ_i`, `S_j(y) = S_(τ_i + j)(x) - S_(τ_i)(x) > 0`.
- **Similarity on `C(q)`.** By Item 3, `ℓ_D(y) ≤ A`. So `g^D` is a similarity
  on a cone containing `C(q)`, with ratio `S_D(y) = Δ`.
- **Contracting map.**
  - Distinct images of points of `C(q)` share prefixes of weight `≥ w(q) + Δ`.
    As in Item 3, `g^D(C(q)) ⊆ C(p)`, where `p` is the shortest prefix of `y'`
    of weight `≥ w(q) + Δ`.
  - `q` is a prefix of `y'` of smaller weight, so `p = qc` with `c` nonempty.
  - Write `g^D(qξ) = qcψ(ξ)`, and let `Φ(ξ) = cψ(ξ)` on the compact set `Z` of
    paths from `t(q)`, with `C(q) = qZ`.
  - Then `w(Φξ ∧ Φξ') = w(ξ ∧ ξ') + Δ`, so `Φ` is an `e^(-Δ)` contraction of
    `(Z, d_w)` with a fixed point `ξ*`.
  - `z = qξ*` satisfies `g^D z = z` and `δ_(g^D)(z) = Δ > 0`. If `p_0` is the
    least period of `z`, then `δ_(g^(p_0))(z) = Δ p_0/D > 0`.

**Item 5 (conclusion).**
- **Bounded sums.** By Item 4, `S_m(g, ·)` is bounded above for `m ≥ 0`.
  - The same holds for `g^-1`, which satisfies `f g^-k f^-1 = g^-l`.
  - `S_m(g^-1, x) = -δ_(g^m)(g^-m x)`.
  - So `|δ_(g^m)| ≤ K` for all `m ∈ Z`.
- **Uniform reading weight.** By Item 3 for `g` and for `g^-1`, `ℓ_m(x) ≤ A*`
  for all `m ∈ Z` and `x`, where `A* = max(L_E, L_g, L_(g^-1)) + K + W`.
- **Lipschitz bound.** If `w(x ∧ y) ≥ A*`, then `y` lies in the cone of weight
  `ℓ_m(x)` around `x`. So
  `w(g^m x ∧ g^m y) = w(x ∧ y) + δ_(g^m)(x) ≥ w(x ∧ y) - K`.
- This is target item 1 with `A = A*`, and it implies equicontinuity.

**Item 6 (rational similarity groups).** Let `G ≤ R_(Γ,E)` have every element of
`Nuc_G` a `w`-similarity. Let `g ∈ G`.
- **Nuclear depth.** By the definition of `Nuc_G` (quoted in
  `research/artifacts/bh-rational-similarity-hosts-2026-09-12.md` §3), there is
  `D` with `n = g|_α ∈ Nuc_G` for `|α| ≥ D`.
- **Ratio.** With `f(α·ω) = f̄(α)·f|_α(ω)`, distinct `x = αξ` and `y = αξ'`
  satisfy `w(gx ∧ gy) = w(x ∧ y) + [w(ḡ(α)) - w(α) + c_n]`, where `c_n` is the
  ratio of `n`.
- So `g` is a similarity on `C(α)`. Every cone of weight `≥ D·W` has length
  `≥ D`, so `g` is `w`-tame.
