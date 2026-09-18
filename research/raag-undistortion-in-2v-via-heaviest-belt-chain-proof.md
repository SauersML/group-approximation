---
rg: 2
id: raag-undistortion-in-2v-via-heaviest-belt-chain-proof
kind: route
title: Bound word length in A_Γ by the head move along the heaviest chain of non-commuting syllables, and bound the head move by a subadditive exponent length on 2V
target: raags-are-undistorted-in-brin-thompson-group-2v
requires:
  - every-raag-embeds-in-full-shift-topological-full-group
  - full-shift-topological-full-group-embeds-in-2v
artifacts:
  - research/artifacts/raags-in-2v-via-full-shift-full-group-2026-09-16.md
---

Lane proof, not independently reviewed. References are to the artifact
`raags-in-2v-via-full-shift-full-group-2026-09-16`: head maps (P1)–(P3) in B.1, the generators `f_u` in
B.2, reduced expressions and the greedy chain (Lemmas 1–2) in B.4, and the Theorem in B.4.

## Step 0. Two subadditive lengths

- **On `[[Σ^Z]]`.** `M(f) = max_x |c_f(x)|` satisfies `M(hh') <= M(h) + M(h')` and `M(h^{-1}) = M(h)`.
  - The first follows from `c_{hh'}(x) = c_{h'}(x) + c_h(σ^{c_{h'}(x)} x)` (Part E1, step 1).
  - The second holds because `c_{h^{-1}}(x) = -c_h(h^{-1}x)`.
  - Also `M(h) = max_{x,i} |p^h_x(i) - i|`, since `p^h_x(i) - i = c_h(σ^i x)`.
- **On `2V`.** Near each point `z`, an `F ∈ 2V` is canonical from a dyadic brick with prefixes
  `(d_1, d_2)` onto one with prefixes `(r_1, r_2)`. Put `e_z(F) = (|r_1|-|d_1|, |r_2|-|d_2|)`.
  - This is well defined: halving a brick adds one letter to both `d_i` and `r_i`, and two canonical
    maps that agree on a brick have the same exponent.
  - It satisfies the chain rule `e_z(GF) = e_{F(z)}(G) + e_z(F)`.
  - So `ℓ(F) = max_z ||e_z(F)||_1` is finite, subadditive, and has `ℓ(F^{-1}) = ℓ(F)`. For any finitely
    generated `K <= 2V` with finite generating set `S`, `ℓ(F) <= ℓ_S |F|_S` where `ℓ_S = max_{s∈S} ℓ(s)`.
- **Comparison.**
  - Recoding multiplies cocycles by `m` (B.5: the cocycle of `ρfρ^{-1}` is `m·c(ρ^{-1}y)`).
  - On a grid brick where `c ≡ k`, the map `Φ^{-1}fΦ` is canonical from prefix lengths `(r, r)` to
    `(r-k, r+k)` (Part A). So `e = (-k, k)` and `||e||_1 = 2|k|`.
  - Hence `ℓ(Ψ̂(g)) = 2m·M(Ψ(g))`.

## Step 1. The heap of a reduced expression

Let `g ≠ 1` and let `s_1 ⋯ s_ℓ` be a reduced expression (Lemma 1), `s_i = t_{j_i}^{n_i}`. Write `a ≁ b`
for "no edge" (this includes `a = b`). For `i < m` put `i ◁ m` if `j_i ≁ j_m`, and let `≺` be the
transitive closure. The weight of a set `C` of indices is `W(C) = Σ_{i∈C} |n_i|`. Put `W = W({1..ℓ})`.
Then `|g| <= W`, since the expression is a word of that length.

- **(H1) Reordering keeps reducedness.** Let `τ` be a linear extension of `≺`. It is reached from the
  identity by swapping adjacent `≺`-incomparable syllables, whose types are adjacent and so commute. Hence
  `s_{τ(1)} ⋯ s_{τ(ℓ)}` is again an expression of `g`. It is reduced. Suppose `a` before `b` have the same
  type `u`, and every syllable between them in the new order has a type adjacent to `u`.
  - Same-type syllables are pairwise comparable, so `a` precedes `b` originally too.
  - A same-type syllable `r` between them originally would satisfy `a ≺ r ≺ b`. It would then lie between
    them in the new order, and `u` is not adjacent to itself. So `a, b` are consecutive occurrences of
    `u`.
  - By reducedness of the original there is `q` with `a < q < b` and `j_q ≁ u`, and `j_q ≠ u`.
  - Then `a ◁ q ◁ b`, so `q` lies between them in the new order. Contradiction.
- **(H2) Width at most `ω`.** Incomparable syllables are not `◁`-related. So their types are distinct
  and adjacent, and an antichain has the types of a clique. By Dilworth's theorem the indices are a union
  of at most `ω` chains. So some chain has `W(C) >= W/ω`.
- **(H3) A heaviest chain is saturated.** Take `C = {c_1 ≺ ⋯ ≺ c_k}` of maximal weight. Every `|n_i| >= 1`,
  so `C` is a maximal chain.
  - `c_1` is `≺`-minimal and `c_k` is `≺`-maximal.
  - Each `c_{p-1} ≺ c_p` is a cover. A cover in a transitive closure is a generating relation, so
    `c_{p-1} ◁ c_p` and `j_{c_{p-1}} ≁ j_{c_p}`.

## Step 2. A reordering whose greedy chain is `C`

Let `U_p = {x : c_p ⪯ x}`, so `U_1 ⊇ ⋯ ⊇ U_k`, and let `φ(x) = #{p : x ∈ U_p}`.

- **The order `E`.** `φ` is order-preserving. The level set `φ^{-1}(p)` is `U_p ∖ U_{p+1}`, and it
  contains `c_p` as its minimum. Let `E` list the levels `0, 1, …, k` in turn. Within level `p >= 1`, put
  `c_p` first, then the rest in a linear extension. `E` is a linear extension of `≺`, so by (H1) it is a
  reduced expression of `g`.
- **Greedy chain of `E`** (Lemma 2, computed in `E`).
  - Level `k` is `U_k = {c_k}`, since `c_k` is maximal. So `c_k` is last.
  - Let `p >= 2`. The syllables before `c_p` in `E` are exactly levels `< p`. Take one, `x`, with
    `j_x ≁ j_{c_p}`. Then `x` and `c_p` are comparable, and `E` puts `x` first, so `x ≺ c_p`. If `x` is in
    level `p-1`, then `c_{p-1} ⪯ x ≺ c_p`, so `x = c_{p-1}` by the cover.
  - Conversely `c_{p-1}` qualifies, and every other candidate lies in an earlier level. So the greedy step
    from `c_p` picks `c_{p-1}`.
  - A candidate before `c_1` would be `≺ c_1`, which minimality excludes. So the chain stops at `c_1`.

## Step 3. The head move

Apply the Theorem of B.4 to `E` with its greedy chain `c_1, …, c_k`.
- **Configuration.** `x = ⋯ # # β_1 ⋯ β_k # # ⋯` with `β_p = (T_{u_p} B_{u_p})^{L_p}`,
  `u_p = j_{c_p}` and `L_p = |n_{c_p}|`.
- **Head move.** `p^{Ψ(g)}_x(P_{k+1}) = P_1`.
  - `P_1` is the first letter of `β_1`.
  - `P_{k+1} = B_{L_k}(β_k)` is the last letter of `β_k`, since `β_k` is followed by `#` and not relocated.
- **Bound.** So `P_{k+1} - P_1 = 2 Σ_p L_p - 1 = 2W(C) - 1`, and by Step 0 and (H2)
  `M(Ψ(g)) >= 2W(C) - 1 >= 2W/ω - 1 >= 2|g|/ω - 1`.

This is item 1: `|g| <= (ω/2)(M(Ψ(g)) + 1)`. It holds trivially for `g = 1`.

## Step 4. Undistortion

- **In `[[Σ^Z]]`.** For finitely generated `K` with `Ψ(A_Γ) <= K <= [[Σ^Z]]` and generating set `S`,
  Step 0 gives `M(Ψ(g)) <= M_S |Ψ(g)|_S`. So `|g| <= (ω/2)(M_S |Ψ(g)|_S + 1)`.
- **In `2V`.** For `Ψ̂(A_Γ) <= K <= 2V`, likewise `|g| <= (ω/2)(ℓ_S |Ψ̂(g)|_S/(2m) + 1)`.
- **Reverse inequality.** It holds for every homomorphism of finitely generated groups.

So both embeddings are quasi-isometric. ∎

## Calibration

- **One vertex.** `ω = 1`, and `t^n` moves the head along a belt of length `|n|`, so `M = 2|n| - 1`. The
  bound reads `|n| <= |n|`, which is exact.
- **`Γ = K_2` (`Z^2`).** For `g = t_u^a t_w^b` the heaviest chain is one syllable, of weight
  `max(|a|,|b|)`. The bound `|a|+|b| <= M + 1` is tight up to the factor `ω = 2`, and this factor is why
  the clique number appears.
- **The argument does not prove too much.**
  - It needs Salo's specific belts. For an arbitrary finitely generated subgroup of `[[Σ^Z]]`,
    `M` could be small on long elements.
  - It says nothing about distorted subgroups of `2V` outside `[[Σ^Z]]`. The Callard–Salo distortion
    element uses a tape-rewriting head, which is not an element of `[[Σ^Z]]`.
