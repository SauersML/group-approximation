---
rg: 2
id: full-shift-local-cocycles-displacement-bound-proof
kind: route
title: "Locality splits b(g) orthogonally over the images of the germ pieces of g, so psi(g) is at most the sum of psi over its germ types; [[X]] has three germ types of displacement one and infinitely many elements made of them"
target: full-shift-full-group-local-cocycles-are-displacement-bounded
requires: []
---

Notation as in the target. The convention is `(σx)_n = x_{n+1}`. All Hilbert spaces are complex,
and `‖·‖` is the norm. The route is self-contained. The only citation is Farley's theorem, which
appears in Step 6 and is used only for the calibration remark, not for the kill.

## Step 0: facts about `[[X]]`

- (0.1) **`k_g` is determined by `g`.** If `σ^{k}x = σ^{k'}x` with `k ≠ k'`, then `x` is periodic.
  So two continuous candidates for `k_g` agree on the aperiodic points. Those points are dense,
  and both functions are locally constant, so they agree everywhere.
- (0.2) **`k_{gh}(x) = k_h(x) + k_g(hx)`.** Indeed `gh x = σ^{k_g(hx)} σ^{k_h(x)} x`, and the
  right-hand side is continuous, so (0.1) applies.
- (0.3) **Finiteness.** `k_g` is continuous on a compact space and integer-valued. So it takes
  finitely many values, and the level sets `L_k(g) = {k_g = k}` form a finite clopen partition.
  For any `g, h`, the set `{k_g = k_h}` is clopen.
- (0.4) **Images of level sets.** `g(L_k(g)) = σ^k L_k(g)`, and these sets, over `k`, partition
  `X`, because `g` is a bijection.

## Step 1: germ subadditivity (item 1)

This step is written in the generality needed again in Step 6. Let `G` act on a compact space
`X` by homeomorphisms. Suppose that for every pair `g, h ∈ G` there is a designated set
`Agr(g,h) ⊆ {x : gx = hx}`. Let `(π, P)` be a covariant pair and `b` a cocycle that is local:
`P(gB) b(g) = P(hB) b(h)` for all clopen `B ⊆ Agr(g,h)`. For `[[X]]`, take
`Agr(g,h) = {k_g = k_h}`.

**Lemma.** Let `U_1, …, U_N` be a clopen partition of `X` and `t_i ∈ G` with `U_i ⊆ Agr(g, t_i)`.
Then `b(g) = Σ_i P(t_i U_i) b(t_i)`, the summands are pairwise orthogonal, and
`‖b(g)‖² = Σ_i ‖P(t_i U_i) b(t_i)‖² ≤ Σ_i ‖b(t_i)‖²`.

*Proof.*
- Let `A_i = g U_i`. Since `g = t_i` on `U_i`, we have `A_i = t_i U_i`.
- The `A_i` are Borel (indeed clopen) and pairwise disjoint, and their union is `X`, because `g`
  is a bijection. So `Σ_i P(A_i) = P(X) = I`, and the `P(A_i)` are pairwise orthogonal
  projections.
- Locality with `B = U_i` and the pair `(g, t_i)` gives `P(A_i) b(g) = P(A_i) b(t_i)`.
- Therefore `b(g) = Σ_i P(A_i) b(g) = Σ_i P(A_i) b(t_i)`. By Pythagoras,
  `‖b(g)‖² = Σ_i ‖P(A_i) b(t_i)‖²`. Finally `‖P(A_i) v‖ ≤ ‖v‖`. ∎

## Step 2: the displacement bound (item 2)

- (2.1) **Powers of `σ`.** For `k ≥ 1`, the cocycle identity gives
  `b(σ^k) = Σ_{j=0}^{k−1} π(σ^j) b(σ)`, so `‖b(σ^k)‖ ≤ k ‖b(σ)‖`. From
  `0 = b(σ^{-1}σ) = b(σ^{-1}) + π(σ^{-1}) b(σ)` we get `‖b(σ^{-1})‖ = ‖b(σ)‖`, and the same
  argument gives `‖b(σ^{-k})‖ ≤ k ‖b(σ)‖`. Also `b(id) = 0`. So `ψ(σ^k) ≤ k² ψ(σ)` for all `k ∈ Z`.
- (2.2) **Apply the Lemma.** Take the partition of (0.3), `U_k = L_k(g)` for `k ∈ k_g(X)`, with
  `t_k = σ^k`. Since `k_{σ^k} ≡ k`, we have `U_k ⊆ {k_g = k_{t_k}}`. Hence
  `ψ(g) ≤ Σ_{k ∈ k_g(X)} ψ(σ^k) ≤ ψ(σ) Σ_{k ∈ k_g(X)} k²`.
- (2.3) Since `k_g(X) ⊆ [−|g|, |g|]`, the sum is at most `(2|g|+1)|g|²`. For `|g| ≤ 1` it is at
  most `2`. ∎

## Step 3: `B_1` is infinite (item 3)

- (3.1) **Swaps.** Let `U` be clopen with `U ∩ σU = ∅`. Define `s_U` to be `σ` on `U`, `σ^{-1}` on
  `σU`, and the identity on `X ∖ (U ∪ σU)`. The three pieces are clopen and disjoint. `s_U`
  exchanges `U` and `σU` and fixes the rest, so it is a bijection. Each piece is mapped
  homeomorphically, so `s_U` is a homeomorphism. Its displacement function
  `k = 1_U − 1_{σU}` is continuous. So `s_U ∈ B_1`, and by (0.1), `U = {k_{s_U} = 1}`. Hence
  `U ↦ s_U` is injective.
- (3.2) **Group structure.** Fix a clopen `E` with `E ∩ σE = ∅`, and let `U, U' ⊆ E` be clopen.
  Since `σU' ⊆ σE` is disjoint from `E`, a direct check on the six pieces
  `U ∩ U'`, `U ∖ U'`, `U' ∖ U` and their `σ`-images gives `s_U s_{U'} = s_{U Δ U'}`. So
  `{s_U : U ⊆ E clopen}` is an elementary abelian 2-group inside `B_1`. It is infinite, because a
  nonempty clopen subset of the Cantor space `X` has infinitely many clopen subsets.
- (3.3) **The w16 involutions.** Let `x*` be aperiodic with `x*_0 ≠ x*_1`, and let `E_m` be the
  cylinder of `x*_{[−m,m]}` for `m ≥ 1`. If `y ∈ E_m ∩ σE_m`, then `y = σx` with `x ∈ E_m`. So
  `y_0 = x_1 = x*_1` and also `y_0 = x*_0`, a contradiction. Hence `g_m := s_{E_m} ∈ B_1`. The
  sets `E_m` are distinct, so by (3.1) the `g_m` are pairwise distinct, and all lie in the group
  of (3.2) for `E = E_1`.
- (3.4) **Not proper.** `[[X]]` is countable, since `g` is determined by the finitely many values
  of `k_g` on a finite clopen partition. So a proper `ψ` has finite sublevel sets. By Step 2 a
  local `ψ` is at most `2ψ(σ)` on the infinite set `B_1`, so it is not proper. ∎

## Step 4: the Master example is local (members of the class)

Data: `(Ω, τ, p, m, K, ξ)` as in the target, with `p∘τ = σ∘p` and `m` a σ-finite `τ`-invariant
measure. Set `g·ω = τ^{k_g(pω)} ω`.

- (4.1) **Equivariance.** `p(g·ω) = σ^{k_g(pω)} pω = g(pω)`.
- (4.2) **Action.** By (4.1) and (0.2),
  `g·(h·ω) = τ^{k_g(h(pω))} τ^{k_h(pω)} ω = τ^{k_{gh}(pω)} ω = (gh)·ω`. Also `id·ω = ω`. Each map
  `ω ↦ g·ω` is Borel, because it equals `τ^k` on each of the finitely many Borel pieces
  `p^{-1}L_k(g)`. Its inverse is the map of `g^{-1}`.
- (4.3) **`m` is preserved.**
  - `τ^k` maps `p^{-1}L_k(g)` bijectively onto `p^{-1}(σ^k L_k(g))`. By (4.1) it maps into that
    set, and `τ^{-k}` maps back.
  - The sets `σ^k L_k(g)` are pairwise disjoint (0.4).
  - So for Borel `S`, `g·S` is the disjoint union of the sets `τ^k(S ∩ p^{-1}L_k(g))`, and
    `m(g·S) = Σ_k m(S ∩ p^{-1}L_k(g)) = m(S)`, using `τ`-invariance.
- (4.4) **The pair.**
  - Define `π(g)f = f∘g^{-1}` on `L²(Ω, m; K)`. By (4.2) and (4.3) this is a unitary
    representation.
  - `P(A)`, multiplication by `1_{p^{-1}A}`, is a projection-valued measure with `P(X) = I`.
  - Covariance: `(π(g)P(A)π(g)^{-1} f)(ω) = 1_{p^{-1}A}(g^{-1}·ω) f(ω)`. By (4.1),
    `p(g^{-1}·ω) = g^{-1}(pω)`, which lies in `A` iff `pω ∈ gA`. So the operator is `P(gA)`.
- (4.5) **The cocycle.** `b(g) = ξ∘g^{-1} − ξ`, assumed to lie in `L²` for every `g`.
  - Cocycle identity:
    `b(gh) = (ξ∘h^{-1} − ξ)∘g^{-1} + (ξ∘g^{-1} − ξ) = π(g) b(h) + b(g)`.
  - Locality. Let `B ⊆ {k_g = k_h}` be clopen and `ω ∈ p^{-1}(gB)`. Put `ω' = g^{-1}·ω`. Then
    `pω' = g^{-1}(pω) ∈ B` by (4.1), so `h·ω' = τ^{k_h(pω')} ω' = τ^{k_g(pω')} ω' = ω`. Hence
    `h^{-1}·ω = g^{-1}·ω`.
  - So `(P(gB) b(g))(ω) = 1_{p^{-1}(gB)}(ω)(ξ(g^{-1}·ω) − ξ(ω))` coincides pointwise with
    `(P(hB) b(h))(ω)`, where `gB = hB` because `g = h` on `B`.
- (4.6) **Special cases.**
  - (a) `Ω = X × Z`, `τ(x,t) = (σx, t−1)`, `p(x,t) = x`, and `m = ν ⊗ count` with `ν`
    `σ`-invariant, so `m` is `τ`-invariant. With `ξ = 1_{\{t ≥ 0\}}`, the action is
    `g·(x,t) = (gx, t − k_g(x))`, which is the w16 model, and `‖b(g)‖² = ∫|k_g| dν`.
  - (b) Same `Ω`, with `m = Σ_t ν_t ⊗ δ_t` and `ν_t(A) = ν(σ^t A)`. Then
    `m(τ(A × {t})) = m(σA × {t−1}) = ν(σ^{t−1}σA) = ν(σ^t A) = m(A × {t})`, so `m` is
    `τ`-invariant for *any* σ-finite `ν`. Any `ξ = 1_H` with `m(gH Δ H) < ∞` gives a local wall
    function. For the Maharam skew product only `τ`-invariance of `m` is used, and that is
    standard.
  - (c) `Ω = O`, a `σ`-invariant subset of `X`, with `τ = σ|_O`, `p` the inclusion, and `m`
    counting measure times a weight that is constant on orbits (hence `τ`-invariant). Then `ξ = η`
    is arbitrary. Pattern-weighted cut walls are direct sums over `y ∈ O` of the case
    `ξ = 1_{H_y}`, with weights `c(y)`. They are handled by Step 5.

## Step 5: closure (item 4, and example (d))

- (5.1) **Locality is closed under sums and integrals.** For a direct sum `⊕_j (π_j, P_j, b_j)`
  with `Σ_j ‖b_j(g)‖² < ∞` for every `g`, the operators `P = ⊕ P_j` form a covariant
  projection-valued measure, and locality holds coordinatewise. The same holds for a measurable
  field over a measure space, with `P` acting fibrewise.
- (5.2) **The inequality defining `𝓛` is preserved** by these operations and by pointwise limits.
  - If `ψ_j ≤ ψ_j(σ) F`, with `F(g) = Σ_{k ∈ k_g(X)} k²`, and `w_j ≥ 0`, then
    `Σ_j w_j ψ_j ≤ (Σ_j w_j ψ_j(σ)) F`.
  - If `ψ_n → ψ` pointwise, then `ψ(g) = lim ψ_n(g) ≤ lim ψ_n(σ) F(g) = ψ(σ) F(g)`.
  - For direct integrals the same argument applies with integrals in place of sums.
- (5.3) Every member of `𝓛` satisfies `ψ ≤ 2ψ(σ)` on `B_1`, so by (3.4) none is proper. ∎

## Step 6: calibration in `V` (item 5)

- (6.1) **Setting.** `V` acts on `C = {0,1}^N` by finite prefix-replacement tables. Take
  `Agr(g,h) = int{x : gx = hx}` in Step 1. Then the Lemma holds verbatim, since its proof used
  only `g = t_i` on `U_i`.
- (6.2) **The family.** Let `t(aw) = (1−a)w` for `a ∈ {0,1}`, `w ∈ C`. This is the table
  `[0] → [1]`, `[1] → [0]`. For a clopen `W ⊆ C`, let `g_W(aw) = (1−a)w` if `w ∈ W`, and
  `g_W(aw) = aw` otherwise. Write `W` and its complement as finite disjoint unions of cylinders
  `[u_j]` and `[v_l]`. Then `g_W` is the table `[a u_j] → [(1−a) u_j]`, `[a v_l] → [a v_l]`, so
  `g_W ∈ V`.
- (6.3) **The bound.** `g_W = t` on the clopen set `U = {aw : w ∈ W}`, and `g_W = id` on its
  complement. Both sets lie in the interiors of the respective agreement sets. So the Lemma gives
  `ψ(g_W) ≤ ψ(t) + ψ(id) = ψ(t)` for every local `ψ`.
- (6.4) **Infinitely many.** Distinct `W` give distinct supports `{aw : w ∈ W}`, hence distinct
  `g_W`, and there are infinitely many clopen `W`. `V` is countable, so no local `ψ` on `V` is
  proper.
- (6.5) **Consequence.** D. Farley, *Proper isometric actions of Thompson's groups on Hilbert
  space*, Int. Math. Res. Not. 2003, no. 45, 2409–2414, proves that `V` is Haagerup. This is
  cited from memory, not re-read at source. Hence every cocycle realizing a proper cnd function
  on `V` is non-local for every covariant pair on `C`. The calibration is used only to interpret
  the kill; Steps 1–5 do not depend on it. ∎

## Scope check

- No step used invariance, finiteness, or non-atomicity of the spectral measure `P`. The only
  inputs are:
  - the covariance identity;
  - `P(X) = I`;
  - locality;
  - the finite clopen germ decomposition of elements of `[[X]]`.
- The proof shows more than non-properness: `ψ` is bounded by a cubic polynomial in the
  displacement `|g|`, uniformly over the whole displacement ball.
