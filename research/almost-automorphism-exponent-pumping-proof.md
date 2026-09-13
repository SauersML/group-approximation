---
rg: 2
id: almost-automorphism-exponent-pumping-proof
kind: route
title: The periodic spectrum of the exponent cocycle is conjugation invariant and homogeneous, so a proper-power relation kills it; pumping then bounds every Birkhoff sum and hence every reading length
target: almost-automorphism-conjugate-to-proper-power-is-equicontinuous
requires: []
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

Full proofs are in §2–§4 of the artifact. Notation is as in the target. `L(g)`
is the largest word length in a table for `g`, and
`dist(x,y) = 2^-(common digits)`.

**Item 1 (cocycle).**
- For `x ∈ X`, choose a cone `C(u) ∋ x` on which `g` acts as `u w ↦ v h(w)`,
  and set `δ_g(x) = |v| - |u|`.
- This is well defined, since subcones give the same difference. It is also
  locally constant, with `|δ_g| ≤ L(g)`.
- It satisfies `δ_{gf}(x) = δ_g(f x) + δ_f(x)`. Write
  `S_m(x) = δ_{g^m}(x)`.
- For `x` of least period `p`, set `ρ_g(x) = δ_{g^p}(x)/p`. Let `R(g)` be the
  set of these values.

**Item 2 (spectrum).**
- `R(f g f^-1) = R(g)`: `f` carries periodic orbits to periodic orbits, and
  the `δ_f` terms cancel.
- `R(g^m) = m R(g)`.
- So `f g^k f^-1 = g^l` gives `k R(g) = l R(g)`. Say `|k| < |l|`, and let
  `s = sup |R(g)| ≤ L(g)`.
  - If `s > 0`, pick `ρ ∈ R(g)` with `|ρ| > s|k|/|l|`.
  - Then `lρ = kρ'` for some `ρ' ∈ R(g)` with `|ρ'| > s`, a contradiction.
- Hence `R(g) ⊆ {0}`. The case `|k| > |l|` is symmetric.

**Item 3 (reading length).**
- Let `ℓ_m(x)` be the least `|u|` over cones `C(u) ∋ x` on which `g^m` acts as
  a similarity.
- If `g^m` maps `C(u)` onto `C(p)` with `|p| < L`, extend `u` by the next
  `L - |p|` digits of `x`. So `ℓ_{m+1}(x) ≤ max(ℓ_m(x), L - S_m(x))`.
- Hence `ℓ_m(x) ≤ max(0, max_{j<m} (L - S_j(x)))`.

**Item 4 (pumping).** If `S_m(x)` is unbounded above over `x` and `m ≥ 0`, then
`g` has a periodic point of positive exponent.
- **Levels.** Choose `x` and `M` with
  `S_M(x) - min_{k≤M} S_k(x) ≥ L(r d^L + 2)`. For the levels
  `h_i = min_{k≤M} S_k(x) + iL` below `S_M(x)`, let `τ_i` be the last `k ≤ M`
  with `S_k(x) ≤ h_i`.
- **Pigeonhole.** There are at least `r d^L + 1` levels. So some `i < i'` give
  points `y = g^{τ_i} x` and `g^{τ_{i'}} x` with the same `L`-digit prefix `q`.
- **Increments.** `S_{τ_{i'}}(x) > h_{i'} - L ≥ h_i ≥ S_{τ_i}(x)`. So
  `D = τ_{i'} - τ_i ≥ 1` and `Δ = S_{τ_{i'}}(x) - S_{τ_i}(x) ≥ 1`.
- **Similarity on `C(q)`.** For `0 ≤ j ≤ M - τ_i`, the Birkhoff sums from `y`
  are `≥ 0`. So by Item 3, `g^D` acts on `C(q)` as `q w ↦ p h(w)` with
  `|p| = L + Δ`.
- **Shape of `p`.** `p` is a prefix of `g^{τ_{i'}} x`, so `p = q c` with
  `|c| = Δ`.
- **Fixed point.** `w ↦ c h(w)` is a `2^-Δ`-contraction, since `h` is an
  isometry. Its fixed point `w*` gives `z = q w*` with `g^D z = z` and
  `δ_{g^D}(z) = Δ > 0`.

**Item 5 (conclusion).**
- **Bounded sums.** `e_{g^-1} = -e_g` at periodic points. So by Items 2 and 4,
  applied to `g` and `g^-1`, both `S_m(g, ·)` and `S_m(g^-1, ·)` are bounded
  above. Since `S_m(g^-1, x) = -S_m(g, g^-m x)`, there is `K` with
  `|S_m(g^{±1}, ·)| ≤ K`.
- **Item 1 of the target.** By Item 3, every `g^m` acts as a similarity on
  each level-`N` cone, with `N = max(L(g), L(g^-1)) + K`. The image words have
  `N ± K` digits, which gives the uniform `2^K`-Lipschitz bound.
- **Item 2 of the target.** `g` permutes the finitely many cones with between
  `N - K` and `N + K` digits. So some `g^j` fixes every level-`N` cone.
- **Item 3 of the target.**
  - If `g ∈ V_{d,r}`, then `g^j` acts on each level-`N` cone as
    `q w ↦ q h_q(w)`.
  - Each `h_q` has trivial sections at depth `L(g^j)`, so it lies in a finite
    group.
  - So `g` has finite order.
- **Consequence.** `s` has infinite order in `BS(k,l)`, and
  `F ≤ T ≤ V = V_{2,1}`.

**Scope.** This proof covers one full shift with isometric sections only.
- *Brin--Thompson `nV`.* Item 3 holds coordinatewise, but the pigeonhole in
  Item 4 fails. Along the record times of one coordinate, another coordinate's
  sums can fall without bound.
- *Rational similarity groups.* Their sections are not isometries.
