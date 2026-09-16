---
rg: 2
id: raags-in-full-shift-full-group-conveyor-belt-proof
kind: route
title: One conveyor belt per vertex, with cells shared only between non-adjacent belt types
target: every-raag-embeds-in-full-shift-topological-full-group
requires: []
artifacts:
  - research/artifacts/raags-in-2v-via-full-shift-full-group-2026-09-16.md
---

Full proof: Part B of the artifact. This specialises Salo's conveyor-belt proof
for graph products (arXiv:2103.06663v1, Section 3) to vertex groups `Z`. Salo's
proof supplies the belts, the cell shared between neighbouring non-commuting
belts, and the greedy chain from the right. What is new here is the concrete
one-letter-per-cell layout, the explicit cocycle window, and a complete
verification.

1. **Head maps.** For `f ∈ [[Σ^Z]]` with cocycle `c`, put
   `p^f_x(i) = i + c(σ^i x)`. Then `p^{fg}_x = p^f_x ∘ p^g_x`. Conversely, a
   continuous `c` whose maps `p_x` are all bijections of `Z` defines an element
   of `[[Σ^Z]]`, and `f ≠ id` as soon as some `p^f_x` moves a point.
2. **Belts.** Alphabet `{T_u, B_u : u ∈ V} ∪ {#}`. A `u`-block is `T_u B_u`, and
   a `u`-belt is a maximal run of consecutive `u`-blocks, with cells
   `T_1, …, T_L` (its `T` letters) and `B_1, …, B_L` (its `B` letters). If the
   next block has type `w ≠ u` with `w ≁ u`, the last cell `B_L` is relocated
   onto that block's `T` letter.
3. **Generators.** `f_u` moves the head around every `u`-belt by the cycle
   `T_1 → … → T_L → B_L → … → B_1 → T_1` and fixes all other positions. Its
   cocycle reads `x_{[-4,3]}` (rules 1–4 in the artifact), and its head maps are
   bijections because distinct `u`-belts have disjoint cell sets. So
   `f_u ∈ [[Σ^Z]]`.
4. **Relations.** For `u ~ w` no cell is shared between a `u`-belt and a
   `w`-belt: relocation happens only onto non-adjacent types, and a position has
   one block type. So the head maps of `f_u` and `f_w` have disjoint supports
   and commute, hence `[f_u, f_w] = id`. This gives `Ψ : A_Γ → [[Σ^Z]]`.
5. **Faithfulness.** Take a reduced syllable expression `t_{j_1}^{n_1} ⋯
   t_{j_ℓ}^{n_ℓ}` of `g ≠ 1`, and pick the greedy chain from the right:
   `i_k = ℓ`, and `i_{p-1}` is the last earlier syllable not adjacent to
   `j_{i_p}`. Reducedness makes consecutive chain types distinct and
   non-adjacent. On `x = #^∞ β_1 ⋯ β_k #^∞` with `β_p` a `u_p`-belt of length
   `|n_{i_p}|`, each chain syllable moves the head from `B_L(β_p)` (the relocated
   cell `T_1(β_{p+1})`) to `T_1(β_p)`. Every other syllable has a type adjacent
   to the current belt, so it is neither of the two belt types owning the
   current position and fixes it. The head goes from the last cell of `β_k` to
   the first cell of `β_1`, so `Ψ(g) ≠ id`.
6. **Binary recoding.** Embed the alphabet in `{0,1}^m` and conjugate by the
   concatenation map `ρ` with `ρσ = σ^m ρ`. This gives `[[Σ'^Z]] ≤ [[{0,1}^Z]]`. ∎

**Exact check.** `experiments/raag-conveyor-belts-full-shift-2026-09-16/belts.py`
verifies bijectivity and commutation on every periodic configuration of small
period and on random long ones. It verifies faithfulness on all 305,466 reduced
words of length `≤ 4` and `|exponent| ≤ 3` for `K_2`, `2K_1`, `P_3`,
`K_3 ⊔ K_1`, `P_4` and `C_4`. Output: `ALL OK`.
