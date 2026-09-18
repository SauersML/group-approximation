---
rg: 2
id: amenably-coupled-actions-liouville-proof
kind: route
title: Couple Schreier pairs by symmetrized Følner averages of an amenable subgroup, glue the couplings into one infinitely supported symmetric measure, and compress finite sets of F-orbit points into one cyclic orbit
target: amenably-coupled-actions-admit-symmetric-liouville-measures
requires: [pl-ea-calibrators-are-nonamenable-interval-groups, affine-lamplighter-amenable-iff-extensively-amenable, thompson-f-amenable-iff-dyadic-action-extensively-amenable]
---

Notation is as in the claim. All `ℓ¹` norms are on `X` or on `G` with counting measure.

**Step 0 (conventions).** For probabilities `ν` on `G` and `α` on `X`, put `ν·α = Σ_{g,x} ν(g)α(x)δ_{gx}` and
`ν·x = ν·δ_x = P_ν(x, ·)`. Let `(ν*ν′)(k) = Σ_{gh=k} ν(g)ν′(h)` and `ν̌(g) = ν(g⁻¹)`. Then:
- (i) `(ν*ν′)·α = ν·(ν′·α)`. In particular `P_µ^m(x, ·) = µ^{*m}·x`.
- (ii) `‖ν·α − ν·β‖ ≤ ‖α − β‖`, because `ν·` is a Markov operator.
- (iii) `‖ν·x − ν′·x‖ ≤ ‖ν − ν′‖`, because pushforward under `g ↦ gx` does not increase `ℓ¹` norm.
- (iv) `(ν*ν′)ˇ = ν̌′*ν̌`. So `ψ̌*ψ` is symmetric for every `ψ`.

**Step 1 (Liouville from coupling).** *Lemma 1.* Let `G ↷ X` be transitive and let `(g_i)_{i≥1}` generate `G`.
Suppose that for every finite set `P ⊆ X × X` and every `ε > 0` there is a finitely supported symmetric
probability `ν` with `‖ν·a − ν·b‖ ≤ ε` for all `(a, b) ∈ P`. Then there is a symmetric `µ` with every
`g_i ∈ supp µ` and `(X, P_µ)` Liouville.

*Construction.*
- Put `c_j = 2^{−j−1}` for `j ≥ 0`, `Q_j = Σ_{i<j} c_i = 1 − 2^{−j}`, and `τ_i = (δ_{g_i} + δ_{g_i⁻¹})/2`.
  Enumerate `X = {y_1, y_2, …}`, repeating points if `X` is finite.
- Let `ζ_0 = τ_1` and `m_0 = 1`. For `j ≥ 1`, with `ζ_0, …, ζ_{j−1}` built:
  - let `m_j` be the least `m ≥ m_{j−1}` with `Q_j^m ≤ 1/j`;
  - let `W_j` be the finite set of products `u_r⋯u_1` with `0 ≤ r ≤ m_j` and each `u_t ∈ ⋃_{i<j} supp ζ_i`;
  - let `P_j = {(w y_p, w g_q y_p) : w ∈ W_j, p, q ≤ j}`, a finite set;
  - choose `ν_j` by the hypothesis for `P_j` and `ε = 1/(2j)`, and put
    `ζ_j = (1 − 1/(4j))ν_j + (1/(4j))τ_{j+1}`.
- Then `ζ_j` is finitely supported and symmetric, and `‖ζ_j·a − ζ_j·b‖ ≤ 1/(2j) + 2/(4j) = 1/j` on `P_j`.
- `W_j ⊆ W_{j+1}` and `P_j ⊆ P_{j+1}`. So for `k ≥ j`, `ζ_k` couples `P_j` within `1/k ≤ 1/j`.
- Let `µ = Σ_{j≥0} c_jζ_j`. It is a symmetric probability, and `g_{j+1} ∈ supp ζ_j` for every `j ≥ 0`.

*Estimate.* Fix `p, q`, let `x = y_p`, `y = g_q x`, and let `j ≥ max(p, q)`. By multilinearity,
`µ^{*m_j} = Σ_{k∈N^{m_j}} c_{k_1}⋯c_{k_{m_j}} ζ_{k_{m_j}} * ⋯ * ζ_{k_1}`. Write `D_k` for the `ℓ¹` distance between the
images of `x` and `y` under the `k`-th term.
- Sequences with every `k_t < j` have total weight `Q_j^{m_j} ≤ 1/j` and `D_k ≤ 2`. They contribute at most `2/j`.
- Otherwise let `i` be the first index with `k_i ≥ j`, and let `ω = ζ_{k_{i−1}} * ⋯ * ζ_{k_1}`. It is supported in
  `W_j`, since it is a product of `i − 1 < m_j` factors from `ζ_{<j}`. By (i) and (ii), the later factors do not
  increase distance, so
  `D_k ≤ ‖ζ_{k_i}·(ω·x) − ζ_{k_i}·(ω·y)‖ ≤ Σ_w ω(w)‖ζ_{k_i}·wx − ζ_{k_i}·wg_qx‖ ≤ 1/j`,
  because `(wx, wg_qx) ∈ P_j` and `k_i ≥ j`. These sequences contribute at most `1/j`.
- Hence `‖µ^{*m_j}·x − µ^{*m_j}·g_qx‖ ≤ 3/j` for every `j ≥ max(p, q)`.

*Conclusion.* Let `h` be bounded and `P_µ`-harmonic. Then `h = P_µ^m h`, so by (i)
`|h(x) − h(g_qx)| ≤ ‖h‖_∞ · ‖µ^{*m_j}·x − µ^{*m_j}·g_qx‖ ≤ 3‖h‖_∞/j` for all large `j`. Hence `h(g_qx) = h(x)` for
all `x` and `q`. Replacing `x` by `g_q⁻¹x` gives invariance under `g_q⁻¹` as well. So `h` is `G`-invariant, and it
is constant because the action is transitive. ∎

**Step 2 (coupling from an amenable subgroup; Theorem A).** Assume `G ↷ X` is LAT. Let `P` be finite and
`ε > 0`. Let `Y` be the finite set of points appearing in `P`, and `H` an amenable subgroup with
`Y ⊆ H·y_0`.
- For `(a, b) ∈ P`, write `a = h′y_0` and `b = h″y_0`, and set `h_{a,b} = h″h′⁻¹ ∈ H`, so that `h_{a,b}a = b`.
  Let `E` be the finite set of these elements.
- Since `H` is amenable, it has a finite nonempty `Ψ` with `|e⁻¹Ψ Δ Ψ| ≤ ε|Ψ|` for all `e ∈ E` (a left Følner
  set). Put `Φ = Ψ⁻¹`. Then `Φe = (e⁻¹Ψ)⁻¹`, so `|Φe Δ Φ| ≤ ε|Φ|`.
- Let `ψ` be uniform on `Φ` and `ν = ψ̌*ψ`. It is symmetric by (iv), and finitely supported in `Φ⁻¹Φ ⊆ H`.
- `ψ*δ_e` is uniform on `Φe`. By (i), (iii) and (ii),
  `‖ν·(ea) − ν·a‖ = ‖ψ̌·((ψ*δ_e)·a) − ψ̌·(ψ·a)‖ ≤ ‖(ψ*δ_e)·a − ψ·a‖ ≤ ‖ψ*δ_e − ψ‖ = |Φe Δ Φ|/|Φ| ≤ ε`.

This is the hypothesis of Lemma 1, which proves Theorem A. Every `ζ_j` there is `ν_j`, supported in an amenable
subgroup, mixed with `τ_{j+1}`. ∎

**Step 3 (Corollary 1).** If `G` is amenable, take `H = G`: a single `G`-orbit is all of `X`.

**Step 4 (Corollary 2: orbits of F).** `F` is the group of piecewise linear homeomorphisms of `[0,1]` with
finitely many dyadic breakpoints and slopes in `2^Z`.
- *Gap maps.* For dyadic `a < b` and `c < d` there is an increasing PL map `[a,b] → [c,d]` with dyadic
  breakpoints and slopes in `2^Z`.
  - An interval with dyadic endpoints is a finite union of consecutive standard dyadic intervals
    `[k2^{−n}, (k+1)2^{−n}]`. Halving one of them raises the count by one, so both intervals split into the same
    number `r` of consecutive standard pieces `I_1 < ⋯ < I_r` and `J_1 < ⋯ < J_r`.
  - Map each `I_t` affinely onto `J_t`. The slope `|J_t|/|I_t|` is a power of 2, and the pieces agree at shared
    endpoints.
- *Gluing.* Take consecutive dyadic intervals covering `[0,1]`, and a map that on each is either a gap map or
  the restriction of an element of `F`. Such restrictions map dyadic intervals onto dyadic intervals. If the
  images are consecutive and cover `[0,1]`, the glued map lies in `F`.
- *Chain lemma.* Let `Y` be an `F`-orbit in `(0,1)` and `t_1 < ⋯ < t_N` in `Y`, with `N ≥ 2`. Choose `g_i ∈ F`
  with `g_i(t_i) = t_{i+1}`.
  - Choose open neighbourhoods `U_i ∋ t_i` for `i < N`, pairwise disjoint, and `V_{i+1} ∋ t_{i+1}` for `i < N`,
    pairwise disjoint, all inside `(0,1)`.
  - By continuity, choose dyadic intervals `I_i = [α_i, β_i] ⊆ U_i` with `α_i < t_i < β_i` and
    `g_i(I_i) ⊆ V_{i+1}`, for `i < N`.
  - Then `I_1 < ⋯ < I_{N−1}` and `J_i = g_i(I_i)` satisfy `J_1 < ⋯ < J_{N−1}`. All of them are dyadic
    intervals in `(0,1)`.
  - Define `f = g_i` on `I_i`, and use gap maps between the complementary intervals, in order:
    - `[0, α_1] → [0, min J_1]`;
    - `[β_i, α_{i+1}] → [max J_i, min J_{i+1}]`;
    - `[β_{N−1}, 1] → [max J_{N−1}, 1]`.
  - Then `f ∈ F` and `f(t_i) = t_{i+1}`.
- Hence `{t_1, …, t_N} = {f^{i−1}(t_1)}` lies in one `⟨f⟩`-orbit. Every finite subset of `Y` is contained in
  such a chain, so `F ↷ Y` is locally cyclically transitive. Theorem A applies with `(g_i) = (x_0, x_1)`. ∎

**Step 5 (Corollary 3: T).** `T` is the group of PL homeomorphisms of `R/Z` with dyadic breakpoints, slopes in
`2^Z`, and dyadics mapped to dyadics. It contains the dyadic rotations `r_θ`, and `Stab_T(0)` acts on
`(0,1) = R/Z ∖ {0}` as `F`.
- `T ↷ D/Z` is transitive, since the rotations move any dyadic point to 0 and to 1/2.
- Let `Z ⊆ D/Z` be finite. Pick a dyadic `p ∉ Z` and set `r = r_{−p}`, so that `r(Z) ⊆ D ∩ (0,1)`. That set is
  one `F`-orbit.
- Step 4 gives `f ∈ Stab_T(0)` with `r(Z) ⊆ ⟨f⟩·t_1`. Then `Z ⊆ ⟨r⁻¹fr⟩·r⁻¹(t_1)`, so `T ↷ D/Z` is locally
  cyclically transitive, and Theorem A gives a non-degenerate symmetric Liouville measure for a finite generating
  set of `T`.
- `T` contains `r_{1/4}`, `r_{1/2}` and `x_0`. By item 5 of `pl-ea-calibrators-are-nonamenable-interval-groups`,
  `T ↷ D/Z` is neither amenable nor extensively amenable.
- `T` is nonamenable, since every action of an amenable group is amenable and `T ↷ D/Z` is not. ∎

**Step 6 (Corollary 4: lamplighters).** The subgroup `{(A, e)}` of `W_X`, isomorphic to the abelian group
`(P_f(X), Δ)`, acts on `P_f(X)` by `E ↦ A Δ E`. This is simply transitive, so every finite subset of `P_f(X)`
lies in its single orbit, and Theorem A applies.
- Amenability of the action is equivalent to extensive amenability of `G ↷ X`, by
  `affine-lamplighter-amenable-iff-extensively-amenable`.
- For `F_2 ↷ F_2` by left translation, the action is not amenable: its stabilizers are trivial and `F_2` is not
  amenable. So by the same node it is not extensively amenable, and `W_{F_2} ↷ P_f(F_2)` is a non-amenable
  Liouville action.
- For `F ↷ D`, extensive amenability is equivalent to amenability of `F`, by
  `thompson-f-amenable-iff-dyadic-action-extensively-amenable`. ∎
