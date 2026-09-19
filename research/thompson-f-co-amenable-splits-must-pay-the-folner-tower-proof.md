---
rg: 2
id: thompson-f-co-amenable-splits-must-pay-the-folner-tower-proof
kind: route
title: Lay a relative Følner set of K over each coset of a coset Følner set, glued by geodesic cocycles, and feed the product into Moore's tower bound
target: thompson-f-co-amenable-splits-must-pay-the-folner-tower
requires:
  - thompson-f-folner-function-exceeds-every-tower
---

Notation is as in the target claim. `Γ` is symmetric, `X = K\F`, the action is `x·g = xg` on right cosets, and
`o = K`.

**Theorem 1.**
- *Transversal.* For each `x ∈ E` fix `t_x ∈ F` with `K t_x = x` and `|t_x| = d_X(o, x) ≤ rad(E)`. This is a
  geodesic in the Schreier graph, read as a word.
- *Cocycle.* For `x ∈ E` and `γ ∈ Γ` with `xγ ∈ E`, put `c(x,γ) = t_x γ t_{xγ}^{−1}`. Then
  `K t_x γ = xγ = K t_{xγ}`, so `c(x,γ) ∈ K`. Also `|c(x,γ)| ≤ 2·rad(E) + 1 = L`.
- *The set.* Let `Φ ⊆ K` be finite and nonempty with `|Φc Δ Φ| ≤ η|Φ|` for all `c ∈ K ∩ B(L)`. Put
  `A = ⊔_{x∈E} Φ t_x`. The pieces lie in the distinct cosets `x`, so the union is disjoint and `|A| = |E||Φ|`.
- *Counting.* Fix `γ`. Right multiplication by `γ` permutes `X`, so `Aγ \ A` is the disjoint union over `x ∈ E` of
  `Φ t_x γ \ A`, and `Φ t_x γ` lies in the coset `xγ`. There are two cases.
  - If `xγ ∉ E`, then `A` does not meet `xγ`, and the piece has `|Φ|` elements.
  - If `xγ ∈ E`, then `A ∩ xγ = Φ t_{xγ}` and `Φ t_x γ = Φ c t_{xγ}` with `c = c(x,γ)`. So the piece is
    `(Φc \ Φ) t_{xγ}`, of size `|Φc \ Φ| = |ΦcΔΦ|/2 ≤ η|Φ|/2`. This uses `|Φc| = |Φ|`.
- *The bound.* Using `|Aγ| = |A|` and `|EγΔE| = 2·#{x ∈ E : xγ ∉ E}`,
  `|AγΔA| = 2|Aγ\A| ≤ |Φ|·|EγΔE| + η|Φ||E|`.

  Summing over `γ` gives `Σ_γ |AγΔA| ≤ |Φ| Σ_γ |EγΔE| + |Γ|η|E||Φ| < (ε + |Γ|η)|A|`. The inequality is strict
  because `E` is `ε`-Følner and `|Φ| > 0`. ∎

**Corollary 2.** Take `ε = C^{−m}/2` and `η = C^{−m}/(2|Γ|)`. If `Φ_K(L, η) = ∞`, there is nothing to prove.
Otherwise Theorem 1 gives a `C^{−m}`-Følner `A ⊆ F` with `|A| = |E|·Φ_K(L, η)`. The imported
Theorem 1.1 of Moore (`thompson-f-folner-function-exceeds-every-tower`, verbatim there: "if A⊆F is a
C^−n-Følner set with respect to Γ, then A contains at least exp_n(0) elements") gives `|A| ≥ exp_m(0)`. ∎

**Corollary 3.** Suppose `k ≥ 1` satisfies both bounds, and fix `m ≥ 1`.
- *Parameters.* Put `n = ⌈2C^m⌉`, `n' = ⌈2|Γ|C^m⌉` and `N = n' + k`. Then `n + k ≤ N`.
- *The two sets.* Take a `1/n`-Følner `E ⊆ X` with `|E| + rad(E) = S_K(n) ≤ exp_k(N) =: T`. Take
  `L = 2·rad(E) + 1`. Then `Φ_K(L, 1/n') ≤ exp_k(L + n' + k) ≤ exp_k(2T + 1 + N) ≤ exp_k(4T)`, using
  `1 ≤ N ≤ T`.
- *Applying Theorem 1.* We have `1/n + |Γ|/n' ≤ C^{−m}`, so Theorem 1 and Moore give
  `exp_m(0) ≤ T·exp_k(4T) ≤ exp_k(4T)² ≤ exp_k(8T) ≤ exp_k(exp_k(N + 3)) = exp_{2k}(N + 3)`.
- *The elementary facts used,* for `k ≥ 1` and `y ≥ 1`:
  - `exp_k(y)² ≤ exp_k(2y)`. There is equality at `k = 1`. Inductively,
    `exp_{k+1}(2y) = 2^{exp_k(2y)} ≥ 2^{exp_k(y)²} ≥ 2^{2exp_k(y)}`, because `exp_k(y) ≥ 2`.
  - `8·exp_k(y) ≤ exp_k(y + 3)`. There is equality at `k = 1`. For `k ≥ 2` it follows from
    `exp_{k−1}(y + 3) ≥ exp_{k−1}(y) + 3`, since every `exp_j` has increments at least 1.
- *Contradiction.* Choose an integer `c = c(C, |Γ|, k)` with `N + 3 ≤ 2^{cm}` for all `m ≥ 1`. Then
  `exp_m(0) ≤ exp_{2k}(2^{cm}) = exp_{2k+1}(cm)`. But `exp_m(0) = exp_{2k+1}(exp_{m−2k−1}(0))`, and
  `exp_{m−2k−1}(0) > cm` for all large `m`. Since `exp_{2k+1}` is strictly increasing, this is a contradiction. ∎

**Corollary 4.** Let `Φ` be `1/n`-Følner in `K` for `T`, with `n = ⌈Δ_K(L)/η⌉`. Then `|ΦtΔΦ| < |Φ|/n` for each
`t ∈ T`. For `c = t_1⋯t_r ∈ K ∩ B(L)`, write it with `r ≤ Δ_K(L)`. Then
`|Φ t_1⋯t_r Δ Φ| ≤ |Φ t_1⋯t_{r−1} Δ Φ| + |Φ t_r Δ Φ|`, because right multiplication by `t_r` preserves the size of
`Φ t_1⋯t_{r−1} Δ Φ`. Inducting gives `|ΦcΔΦ| < r|Φ|/n ≤ η|Φ|`. ∎

**Corollary 5.** Let `v(r) = |B_X(o, r)|` and `θ = 1/(4|Γ|n)`.
- *Følner balls.* Since `B_X(o,r)·γ ⊆ B_X(o,r+1)`, we get
  `Σ_γ |B_X(o,r)γ Δ B_X(o,r)| ≤ 2|Γ|(v(r+1) − v(r))`. So if `v(r+1) < (1+θ)v(r)`, the ball `B_X(o, r)` is
  `1/n`-Følner, with radius `≤ r`.
- *Such a ball exists early.* If `v(r+1) ≥ (1+θ)v(r)` for all `1 ≤ r ≤ R`, then
  `D(R+1)^d ≥ v(R+1) ≥ (1+θ)^R ≥ e^{θR/2}`.
- *Polynomial bound.* For `R = c(n+1)²` with `c = c(D, d, |Γ|)` large, `θR/2 ≥ c(n+1)/(8|Γ|)`, which exceeds
  `log D + d·log(R+1)` for all `n ≥ 1`. So some `r ≤ R` works, and `S_K(n) ≤ D·R^d + R`. This is a polynomial in
  `n`, hence at most `exp_{k_0}(n + k_0)` for some `k_0`. Corollary 3 then applies. ∎

**Remark.** Let `A ⊆ F` be `1/n`-Følner and put `f(x) = |A ∩ x|` for cosets `x`.
- *Pushforward.* `|Aγ ∩ x| = f(xγ^{−1})`, so `Σ_x |f(xγ^{−1}) − f(x)| ≤ |AγΔA|`.
- *Level sets.* Let `E_t = {f > t}` for integers `t ≥ 0`. Then `{x : f(xγ^{−1}) > t} = E_tγ`, so
  `Σ_x |f(xγ^{−1}) − f(x)| = Σ_t |E_tγ Δ E_t|` and `Σ_t |E_t| = |A|`.
- *Conclusion.* `Σ_t Σ_γ |E_tγΔE_t| < (1/n) Σ_t |E_t|`, so some nonempty `E_t` is `1/n`-Følner. Also
  `|E_t| ≤ |E_0| ≤ |A|`. ∎

**Scope.** Every step is elementary counting, apart from the one imported theorem. There is no claim of
mathematical novelty for Theorem 1, which is the extension product argument, cf. Erschler's Følner-function bounds
for extensions. The content for the graph is Corollaries 3–5 and the kill of the "escapes the tower barrier"
reading of the co-amenable-split route.
