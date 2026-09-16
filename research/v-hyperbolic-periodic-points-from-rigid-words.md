---
rg: 2
id: v-hyperbolic-periodic-points-from-rigid-words
kind: route
title: "Rigid prefix words: bounded cocycle gives finite order, ladder times give attractors, new minima give repellers"
target: infinite-order-elements-of-v-have-hyperbolic-periodic-points
requires: []
artifacts:
  - research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md
---

Full proof: `research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md`, Section 2 (Lemmas 1.1,
2.1–2.5 and Corollary 2.8). The proof is self-contained and uses no literature.

## Setup

- **The element.** Write `g(β_i z) = α_i z`, where `{β_i}` and `{α_i}` are complete prefix codes.
  - `g^(-1)(α_i z) = β_i z` uses the same codes, swapped.
  - Put `L = max_i max(|α_i|, |β_i|)`.
- **Cocycle.** Let `c(y) = |α_i| − |β_i|` for `y ∈ [β_i]`, so `|c| <= L`, and put `c_n(x) = Σ_(i<n) c(g^i x)`.
  - The swapped codes give `g^(-1)` the cocycle `c^-(y) = −c(g^(-1) y)`, since `y ∈ [α_i]` iff
    `g^(-1) y ∈ [β_i]`.
- **Words.** `[a]` is the cylinder of the finite word `a`.
  - **Lemma 1.1.** If `ρ z = ρ' z` for all `z`, then `ρ = ρ'`.
  - *Proof.* Say `|ρ| <= |ρ'|`, so `ρ' = ρ θ`. If `θ` were nonempty, then `z = θ z` for every `z`, which fails
    for `z` beginning with a letter different from the first letter of `θ`.

## Step 1: rigid words (Lemma 2.1)

Let `|a| >= L`. Every infinite extension of `a` has a prefix in `{β_i}` of length at most `L`, and that prefix is
a prefix of `a`. The code is prefix-free, so there is a unique `i` with `a = β_i a'`. Put `g_*(a) = α_i a'`.

- **(a)** `g(a z) = g_*(a) z` for all `z`, and `|g_*(a)| − |a| = c(y)` for every `y ∈ [a]`. Also
  `g_*(a s) = g_*(a) s` for every word `s`.
- **(b)** `g_*` is injective. If `g_*(a) = g_*(b)`, then `g(a z) = g(b z)`, so `a z = b z` for all `z`, and
  `a = b` by Lemma 1.1.
- **(d) Rigid iteration.** Let `a_0 = a` and `a_(n+1) = g_*(a_n)`, and suppose `|a_0|, …, |a_(N−1)| >= L`.
  - Then `g^N(a z) = a_N z` for all `z`, and `|a_N| = |a| + c_N(x)` for every `x ∈ [a]`.
  - *Proof.* By induction with (a): `g^(n+1)(a z) = g(a_n z) = a_(n+1) z`. Also `g^n x ∈ [a_n]`, so the length
    increment at step `n` is `c(g^n x)`.
  - If `|a| >= L + N L`, the hypothesis holds automatically, since `|c| <= L`.
- **(e) Slopes are the cocycle.** Suppose `n >= 1` and `g^n(ρ z) = ρ' z` for all `z`. Then
  `c_n(x) = |ρ'| − |ρ|` for all `x ∈ [ρ]`.
  - *Proof.* Take `x ∈ [ρ]` and let `a = ρ s` be the prefix of `x` of length `|ρ| + L + n L`.
  - By (d), `g^n(a z) = a_n z` with `|a_n| = |a| + c_n(x)`.
  - Also `g^n(ρ s z) = ρ' s z`. So `a_n = ρ' s` by Lemma 1.1, and `c_n(x) = |ρ'| − |ρ|`.

The same statements hold for `g^(-1)`, with the same `L` and cocycle `c^-`.

**Meaning of the claim.** Let `g^k p = p`.
- By (d) applied to a long prefix of `p`, `g^k` has a local prefix replacement `u w -> v w` around `p`.
- By (e), every such replacement has `|v| − |u| = c_k(p)`.
- So `(g^k)'(p) != 1` iff `c_k(p) != 0`.

It therefore suffices to find a periodic point `p`, `g^k p = p`, with `c_k(p) != 0`.

## Step 2: the trichotomy

Put `μ(x) = inf_(n >= 0) c_n(x)` and `M(x) = sup_(n >= 0) c_n(x)`, so `μ <= 0 <= M` because `c_0 = 0`. The
following classes partition `X`:
- `A0 = {μ > −∞, M < ∞}`;
- `A+ = {μ > −∞, M = ∞}`;
- `B = {μ = −∞}`.

For `x` with `μ(x) > −∞`, put `K = L − μ(x) >= L` and `a = prefix_K(x)`. By (d) and induction on `n`, all rigid
iterates `a_n` are defined, `a_n` is a prefix of `g^n x`, and `|a_n| = K + c_n(x) >= L`.

## Step 3: bounded cocycle (Lemma 2.3)

Let `x ∈ A0`.
- The words `a_n` have lengths in `[L, K + M(x)]`, so `a_i = a_(i')` for some `i < i'`.
- Applying (b) `i` times gives `a_0 = a_p` with `p = i' − i >= 1`.
- By (d), `g^p(a z) = a z` for all `z`. So `g^p = id` on the open set `[a] ∋ x`.

## Step 4: unbounded above (Lemma 2.4)

Let `x ∈ A+` and write `c_n = c_n(x)`.

1. **`c_n -> ∞`.**
   - Otherwise some `C` has `c_n <= C` for infinitely many `n`. Two of those `a_n` coincide, and as in Step 3,
     `g^p x = x` and `c_p(x) = |a_p| − |a| = 0`.
   - Then `c_(mp + r)(x) = c_r(x)`, so `M(x) < ∞`. This is a contradiction.
2. **Ladder times.** Call `j` a ladder time if `c_n > c_j` for all `n > j`.
   - For each `N`, `min_(n >= N) c_n` exists and is attained only finitely often, by item 1.
   - The last `j >= N` attaining it is a ladder time. So there are infinitely many ladder times.
3. **Structure at a ladder time.** Let `j` be a ladder time and write `a_j = b_j s_j` with `|b_j| = L`. For
   `n >= j` put `e_j = b_j` and `e_(n+1) = g_*(e_n)`. By induction on `n`:
   - `a_n = e_n s_j` and `|e_n| = L + c_n − c_j >= L`;
   - the step is `a_(n+1) = g_*(e_n s_j) = g_*(e_n) s_j` by (a), with length increment `c(g^n x)`, since
     `g^n x ∈ [a_n] ⊆ [e_n]`;
   - the new length is at least `L + 1`, since `c_(n+1) > c_j`.

   By (d), `g^(n−j)(b_j z) = e_n z` for all `z`.
4. **Pigeonhole.** There are `2^L` words of length `L`, so there are ladder times `j < j'` with
   `b_j = b_(j') =: v`.
   - Both `e_(j')` and `b_(j')` are prefixes of `a_(j')`.
   - `|e_(j')| = L + c_(j') − c_j > L`, so `e_(j') = v γ` with `|γ| >= 1`.
   - With `p = j' − j`, this gives `g^p(v z) = v γ z` for all `z`.
5. **The attracting point.** Put `q = v γ^∞`.
   - `g^p q = v γ γ^∞ = q`.
   - By (e) with `ρ = v` and `ρ' = v γ`, `c_p(q) = |γ| > 0`. So `q` is a hyperbolic periodic point.

## Step 5: unbounded below (Lemma 2.5)

Let `x ∈ B` and write `c_n = c_n(x)`, `h = g^(-1)`.

1. **New-minimum times.** Call `j` a new-minimum time if `c_j < c_i` for all `i < j`.
   - Given `N`, the first `n` with `c_n < min_(i <= N) c_i` exists because `μ(x) = −∞`.
   - That `n` is a new-minimum time larger than `N`. So there are infinitely many new-minimum times.
2. **Backward rigid words.** For `|v| = L` put `V_0(v) = v` and `V_(i+1)(v) = h_*(V_i(v))`, defined while
   `|V_i(v)| >= L`.
   - *Claim.* Let `j` be a new-minimum time and `v = prefix_L(g^j x)`. Then for `0 <= i <= j`, `V_i(v)` is
     defined, is a prefix of `g^(j−i) x`, and has length `L + c_(j−i) − c_j`.
   - *Proof of the claim.* Induction on `i`, with `i = 0` holding by definition. Let `i < j`.
     - The length `L + c_(j−i) − c_j` is at least `L`, so `V_(i+1)(v)` is defined.
     - `h(V_i(v) z) = V_(i+1)(v) z`, so `V_(i+1)(v)` is a prefix of `h(g^(j−i) x) = g^(j−i−1) x`.
     - The length increment is `c^-(g^(j−i) x) = −c(g^(j−i−1) x)`, which gives length
       `L + c_(j−i−1) − c_j`. This is `>= L + 1`, because `j − i − 1 < j`.
   - *Consequence.* By (d) for `h`, `g^(-j)(v w) = V_j(v) w` for all `w`, and `V_j(v)` is a prefix of `x` of
     length `L − c_j`.
3. **One word at infinitely many times.** Some `v` equals `prefix_L(g^j x)` for infinitely many new-minimum
   times `j_1 < j_2 < …`. Put `j = j_1`.
   - The sequence `V_i(v)` depends only on `v`. So for `k >= 2`, `V_j(v)` and `V_(j_k)(v)` are both prefixes of
     `x`, of lengths `L − c_j < L − c_(j_k)`.
   - Hence `V_(j_k)(v) = V_j(v) ε_k` with `|ε_k| = c_j − c_(j_k) >= k − 1`.
   - For all `z`, `g^(−(j_k − j))(v z) = g^j(V_(j_k)(v) z) = g^j(V_j(v) ε_k z) = v ε_k z`.
4. **Commensurability.** Put `p_k = j_k − j`, so `h^(p_k)(v z) = v ε_k z`.
   - Then `h^(p_k p_2)(v z) = v ε_k^(p_2) z = v ε_2^(p_k) z`.
   - By Lemma 1.1, `ε_k^(p_2) = ε_2^(p_k)`, so `ε_k` is a prefix of `ε_2^∞`.
5. **The repelling point.**
   - `V_j(v) ε_k` is a prefix of `x`, and `g^j(V_j(v) w) = v w`. So `v ε_k` is a prefix of `g^j x` for every
     `k >= 2`.
   - Since `|ε_k| -> ∞`, `q' := g^j x = v ε_2^∞`.
   - `h^(p_2) q' = v ε_2 ε_2^∞ = q'`, so `g^(p_2) q' = q'`.
   - `g^(p_2)(v ε_2 z) = v z` for all `z`. By (e), `c_(p_2)(q') = −|ε_2| < 0`. So `q'` is a hyperbolic periodic
     point.

## Step 6: conclusion (Corollary 2.8)

Suppose `g` has no hyperbolic periodic point. By Steps 4 and 5, `A+ = B = ∅`, so `X = A0`.
- By Step 3 and compactness of `X`, finitely many cylinders `[a_l]` with `g^(p_l) = id` on `[a_l]` cover `X`.
- So `g^m = id` for `m = lcm_l p_l`, and `g` has finite order.

Contrapositively, an infinite-order `g` has a periodic point `p`, `g^k p = p`, with `c_k(p) != 0`, that is,
`(g^k)'(p) != 1`. ∎

## Remarks

- **More is proved in the artifact.**
  - `A0` equals the set of periodic points with zero slope.
  - `B` equals the set `P_r` of repelling periodic points.
  - The set `P_a` of attracting periodic points and `P_r` are finite (Lemma 2.6).
  - For infinite order both are nonempty (Lemma 2.7 and Corollary 2.8).
- **Independent proof.** Lane `zaremsky-2-15b` wrote an independent direct proof of the same claim, in
  `research/artifacts/infinite-order-v-elements-hyperbolic-points-2026-09-16.md`. That file had not landed when
  this route was written, and this route does not depend on it.
