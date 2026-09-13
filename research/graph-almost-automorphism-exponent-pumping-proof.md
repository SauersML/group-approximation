---
rg: 2
id: graph-almost-automorphism-exponent-pumping-proof
kind: route
title: On the path space of a finite graph the periodic exponent spectrum is conjugation invariant and homogeneous, a proper-power relation kills it, and pumping bounds every Birkhoff sum
target: graph-path-almost-automorphism-proper-power-is-equicontinuous
requires: []
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

Notation is as in the target. A *similarity on* `C(q)` means that `g` acts as
`q w ↦ p h(w)` with `h : Z_(r(q)) → Z_(r(p))` a path isometry. For a table of
`g`, set `L(g) = max_i max(|u_i|, |v_i|)`.

**Item 0 (tables).** A path isometry maps `C(q')` onto a cone `C(h(q'))` of the
same length, and induces a path isometry on it. So if `C(q) ⊆ C(u_i)`, then `g`
is a similarity on `C(q)`. Every cone of length `≥ L(g)` lies inside some
`C(u_i)`, so `g` is a similarity on it. Given `g, f ∈ A(E)`, choose a cone
partition fine enough that `f` maps each piece into some domain cone of `g`.
Composing similarities gives a table for `gf`, and inverting `h_i` gives a table
for `g^-1`. So `A(E)` is a group.

**Item 1 (exponent cocycle).**
- For `x ∈ C(u_i)` put `δ_g(x) = |v_i| - |u_i|`.
- Refining the table does not change it: path isometries preserve prefix
  lengths.
- It is locally constant, with `|δ_g| ≤ L(g)`, and
  `δ_(gf)(x) = δ_g(f x) + δ_f(x)`.
- Write `S_m(x) = δ_(g^m)(x)`, which is `Σ_(j<m) δ_g(g^j x)` for `m ≥ 0`. Also
  `δ_(g^-1)(x) = -δ_g(g^-1 x)`.

**Item 2 (periodic spectrum).** For `x` of least `g`-period `p`, put
`ρ_g(x) = δ_(g^p)(x)/p`, and let `R(g)` be the set of these values.
- `R(f g f^-1) = R(g)`. `f` maps `g`-periodic points of least period `p` to
  `fgf^-1`-periodic points of least period `p`, and
  `δ_((fgf^-1)^p)(f x) = δ_f(g^p x) + δ_(g^p)(x) - δ_f(x) = δ_(g^p)(x)`.
- `R(g^m) = m R(g)` for `m ≠ 0`.
  - The periodic points of `g^m` and of `g` coincide.
  - If `x` has least `g`-period `p`, its least `g^m`-period is
    `p' = p/gcd(p,m)`, and `δ_(g^(m p'))(x) = (m p'/p) δ_(g^p)(x)` by summing
    over full periods. For `m < 0` use `R(g^-1) = -R(g)`.
- So `f g^k f^-1 = g^l` gives `k R(g) = l R(g)`. `R(g)` is bounded by `L(g)`.
  Suppose `|k| < |l|` and `s = sup |R(g)| > 0`. Pick `ρ ∈ R(g)` with
  `|ρ| > s|k|/|l|`. Then `lρ = kρ'` with `ρ' ∈ R(g)` and `|ρ'| > s`, which is
  impossible. The case `|k| > |l|` is symmetric. Hence `R(g) ⊆ {0}`.

**Item 3 (reading length).** Let `ℓ_m(x)` be the least `|u|` over cones
`C(u) ∋ x` on which `g^m` is a similarity, and put `L = L(g)`.
- Take `C(u) ∋ x` with `|u| = ℓ_m(x)` and image `C(p)`, so
  `|p| = |u| + S_m(x)`.
- Extend `u` along `x` by `max(0, L - |p|)` edges. The image cone then has
  length at least `L`, so `g` is a similarity on it, and `g^(m+1)` is a
  similarity on the extended cone.
- Hence `ℓ_(m+1)(x) ≤ max(ℓ_m(x), L - S_m(x))`, and with `ℓ_0 = 0`,
  `ℓ_m(x) ≤ max(0, max_(j<m) (L - S_j(x)))`.

**Item 4 (pumping).** If `sup_(x, m ≥ 0) S_m(x) = +∞`, then `g` has a periodic
point `z` with `ρ_g(z) > 0`.
- **Choosing the orbit.** Let `P` be the number of finite paths of length `L`
  in `E`. Choose `x` and `M` with `S_M(x) - min_(k ≤ M) S_k(x) > L(P + 1)`.
- **Levels.** For `i = 0, ..., P`, put `h_i = min_(k≤M) S_k(x) + iL < S_M(x)`,
  and let `τ_i` be the last `k ≤ M` with `S_k(x) ≤ h_i`.
- **Properties.**
  - `τ_i < M`, and `S_k(x) > h_i` for `k > τ_i`.
  - Since each step changes `S` by at most `L`, `S_(τ_i)(x) > h_i - L`.
  - `τ_i` is non-decreasing in `i`.
- **Pigeonhole.** There are `P + 1` points `g^(τ_i) x`, so some `i < i'` give
  `y = g^(τ_i) x` and `y' = g^(τ_(i')) x` with the same length-`L` prefix `q`.
- **Increments.**
  - `S_(τ_(i'))(x) > h_(i') - L ≥ h_i ≥ S_(τ_i)(x)`.
  - So `Δ = S_(τ_(i'))(x) - S_(τ_i)(x) ≥ 1`, and `D = τ_(i') - τ_i ≥ 1`.
- **Similarity on `C(q)`.**
  - For `0 ≤ j ≤ M - τ_i`, `S_j(y) = S_(τ_i + j)(x) - S_(τ_i)(x) ≥ 0`.
  - By Item 3, `ℓ_D(y) ≤ L`, so `g^D` is a similarity on `C(q)`.
  - Its image is `C(p)` with `|p| = L + Δ`. Since `y' ∈ C(p)` has prefix `q`,
    `p = q c` with `|c| = Δ` and `s(c) = r(q)`.
- **Fixed point.**
  - Write `g^D(q w) = q c h(w)`, with `h : Z_(r(q)) → Z_(r(c))` a path isometry.
    Then `Φ(w) = c h(w)` maps `Z_(r(q))` into itself.
  - `dist(Φ w, Φ w') = 2^-Δ dist(w, w')`, and `Z_(r(q))` is compact, so `Φ` has
    a fixed point `w*`.
  - `z = q w*` satisfies `g^D z = z` and `δ_(g^D)(z) = Δ > 0`. So
    `ρ_g(z) = Δ/D > 0`.

**Item 5 (conclusion).**
- **Bounded sums.**
  - `g^-1` satisfies `f g^-k f^-1 = g^-l`. By Items 2 and 4, applied to `g` and
    to `g^-1`, the sums `S_m(g, ·)` and `S_m(g^-1, ·)` are bounded above for
    `m ≥ 0`, say by `K`.
  - Since `S_m(g^-1, x) = -S_m(g, g^-m x)`, this gives `|δ_(g^m)| ≤ K` for all
    `m ∈ Z`.
- **Target Item 1.**
  - By Item 3, applied to `g` and to `g^-1`, every `g^m` is a similarity on
    every cone of length `N = max(L(g), L(g^-1)) + K`.
  - It maps `C(q)` onto `C(p)` with `N - K ≤ |p| ≤ N + K`.
  - For `x, x' ∈ C(q)`, `dist(g^m x, g^m x') = 2^(N - |p|) dist(x, x')`, which
    is at most `2^K dist(x, x')`.
  - Distinct level-`N` cones are at distance `≥ 2^-N`. So the family is
    equicontinuous.
- **Target Item 2.**
  - For `m ∈ Z` let `F_m` send each length-`N` path `q` to the cone
    `g^m C(q)`. It is a cone of length between `N - K` and `N + K`, so `F_m`
    takes finitely many values.
  - Pick `m_1 < m_2` with `F_(m_1) = F_(m_2)`. Then
    `g^(m_2 - m_1) C(q) = g^(-m_1) g^(m_2) C(q) = C(q)` for every `q`.
- **Target Item 3.** If every section of `g` is the identity, the same holds
  for `g^j`. So `g^j` acts on each level-`N` cone `C(q)` as `q w ↦ q w`, and
  `g^j = 1`.
- **Consequence.** `s` has infinite order in `BS(k,l)`, and topological full
  groups of `X_E` consist of elements of `A(E)` with identity sections.
