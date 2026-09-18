---
rg: 2
id: centralizer-amalgams-relative-holomorph-proof
kind: route
title: Conjugates of P by the words c(h) generate a free product that μ(G) permutes like G/C_G(F), so they form a free wreath product
target: centralizer-amalgams-embed-in-relative-holomorphs
requires:
  - centralizer-amalgams-are-free-permutational-wreaths
---

Standard facts used, not re-read: normal forms in free products; in `Q = G * <t>`
the subgroups `G_1 = G` and `G_2 = t G t^{-1}` generate their free product
`G_1 * G_2` (an alternating product of nontrivial letters from `G` and `tGt^{-1}` is
reduced in `Q`).

Notation as in the claim. "Letter" means a letter of a reduced word in `G_1 * G_2`.

**Step 1 (μ).** `μ_h` fixes `G` pointwise and sends `t ↦ th`; its inverse is
`μ_{h^{-1}}`, and `μ_h μ_{h'} = μ_{hh'}` because `μ_h(t h') = t h h'`. So
`μ: G → Aut_G(Q)` is an injective homomorphism (`μ_h(t) = t` forces `h = 1`). Also
`μ_g(t x t^{-1}) = t (g x g^{-1}) t^{-1}` for `x ∈ G`, so `μ_g(a_i(h)) = a_i(gh)`,
`μ_g(k(h)) = k(gh)` and `μ_g(c(h)) = c(gh)`.

**Step 2 (dependence on cosets).** `a_i(h)` depends only on `h C_G(z_i)`, so `k(h)`
and `c(h)` depend only on `ω = hC`. Write `c_ω`, `k_ω`. Each `a_i(h)` is a nontrivial
element of `G_2`, and `s, w` are nontrivial in `G_1`, so `k_ω` and `c_ω = k_ω w k_ω`
are reduced words whose first and last letters lie in `G_2`.

**Step 3 (key word).** Let `ω = hC ≠ ω' = h'C`. Some `i` has
`h z_i h^{-1} ≠ h' z_i h'^{-1}`; let `i_0` be the least one. In
`k_ω^{-1} k_{ω'} = a_k(h)^{-1} s^{-1} ⋯ s^{-1} a_1(h)^{-1} · a_1(h') s ⋯ s a_k(h')`
the letters `a_i` (`i < i_0`) cancel in pairs with the `s^{±1}` between them, and
then `a_{i_0}(h)^{-1} a_{i_0}(h') ≠ 1` stops the cancellation. So `k_ω^{-1} k_{ω'}`
is nontrivial, reduced, with first and last letters in `G_2`. Therefore
`c_ω^{-1} c_{ω'} = k_ω^{-1} · w^{-1} · (k_ω^{-1} k_{ω'}) · w · k_{ω'}` is reduced as
written (each block starts and ends in `G_2`; `w^{±1} ∈ G_1 \ {1}` separates them),
nontrivial, with first and last letters in `G_2`.

**Step 4 (free product).** Put `P_ω = c_ω P c_ω^{-1}` and `p_ω = c_ω p c_ω^{-1}`.
Let `x_j ∈ P_{ω_j} \ {1}` (`1 ≤ j ≤ n`) with `ω_j ≠ ω_{j+1}`, `x_j = (p_j)_{ω_j}`,
`p_j ∈ P \ {1} ⊆ G_1`. Then
`x_1 ⋯ x_n = c_{ω_1} p_1 (c_{ω_1}^{-1} c_{ω_2}) p_2 ⋯ (c_{ω_{n-1}}^{-1} c_{ω_n}) p_n c_{ω_n}^{-1}`.
Every `p_j` is a nontrivial `G_1`-letter flanked by `G_2`-letters (Steps 2 and 3),
so this is a reduced word of positive length and is `≠ 1`. So the `P_ω` generate
their free product `Y = *_{ω ∈ G/C} P_ω`, and `p ↦ p_ω` is an isomorphism
`P → P_ω`.

**Step 5 (wreath).** In `Q ⋊ Aut_G(Q)`, conjugating `q ∈ Q` by `μ_g` gives `μ_g(q)`.
By Step 1, `μ_g(p_ω) = c_{gω} p c_{gω}^{-1} = p_{gω}` (`μ_g` fixes `p ∈ G`). So
`μ(G)` normalizes `Y` and permutes the factors through the left action of `G` on
`G/C`. As `μ(G) ∩ Q = 1`, the subgroup `<μ(G), P_{ω_0}>` (`ω_0 = C`) equals
`Y ⋊ μ(G) ≅ P ≀*_{G/C} G`. By (W) of `centralizer-amalgams-are-free-permutational-wreaths`
it is `≅ G *_C (C × P)`, with `h ↦ μ_h` and `p ↦ p_{ω_0} = c p c^{-1}`. This is item 1.

**Item 2** is (S) of the same node applied to `M ≤ G`, the action on `G/C`, and
`ω_0 = C`, whose stabilizer in `M` is `M ∩ C`.
