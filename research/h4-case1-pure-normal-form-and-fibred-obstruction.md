---
rg: 2
id: h4-case1-pure-normal-form-and-fibred-obstruction
kind: claim
title: Single-edge H_4 bottom-triple hexagons have a pure-braid normal form that is invisible in every sub-arrangement of A_x ∪ A_y and visible in a 19-wall fibred augmentation
distinct_from:
  h4-deligne-complex-bottom-triples-have-upper-bounds: that is the full bottom-triple statement; this is an exact reformulation of its single-edge case plus an obstruction and a replacement for the auxiliary quotient.
---

**Setting.** `Λ = s_1 s_2 s_3 s_4` is of type `H_4`, with `m_{s_3 s_4} = 5`. Put `X = {s_2,s_3,s_4}` (`H_3`),
`Y = {s_1,s_2,s_3}` (`A_3`) and `Z = X ∩ Y` (`A_2`).

- Let `P ⊲ A = A_Λ` be the pure Artin group. Let `P_T = P ∩ A_T` and `ρ_T : P → P_T` the parabolic retraction
  induced by `M(𝒜) ⊂ M(𝒜_T)`.
- Set `F = ker(ρ_X|P_Y)` and `N = ker(ρ_Y|P_X)`. Then `P_Y = F ⋊ P_Z` with `F ≅ F_3` free, and
  `P_X = N ⋊ P_Z`.
- Let `x̄ = W_X`, `ȳ = W_Y` be the adjacent `ŝ_1`, `ŝ_4` vertices of the Coxeter complex. Let `𝒜_x, 𝒜_y, 𝒜_z` be
  the walls through `x̄`, `ȳ` and both (15, 6 and 3 walls), and let `ℓ_x` be the fixed line of `W_X`.

A hexagon is *single-edge* if its image under `π : Δ → C_W` is one edge. This is Case 1 of Lemma `lem:triple`
of arXiv:2405.12068.

**(A) Normal form (both directions).** Up to the action of `A` and the equivalence of Definition
`def:ncycle`, the single-edge hexagons `x_1y_1x_2y_2x_3y_3` (with the `x_i` of type `ŝ_1` and the `y_i` of type
`ŝ_4`) are exactly the tuples

`α_1, α_2, α_3 ∈ F`, `β_1, β_2, β_3 ∈ N` with `α_1α_2α_3 = 1`, `β_1β_2β_3 = 1` and
`α_1β_1α_2β_2α_3β_3 = 1` in `P`.

The vertices are
- `x_1 = A_X`, `x_2 = α_1A_X`, `x_3 = α_1β_1α_2A_X`;
- `y_1 = A_Y`, `y_2 = α_1β_1A_Y`, `y_3 = β_3^{-1}A_Y`.

Moreover:
- `x_{i+1} = x_i` iff `α_i = 1`, and `y_{i+1} = y_i` iff `β_i = 1`.
- `uA_Y` is a common upper bound iff `u ∈ A_XA_Y ∩ α_1A_XA_Y ∩ α_1β_1α_2A_XA_Y`.

So Case 1 is a statement about the pair of subgroups `(F, N)` of `P`.

**(B) Obstruction: `𝒜_x ∪ 𝒜_y` is blind.** Let `𝒜' = 𝒜_x ∪ 𝒜_y` (18 walls).
- `ℓ_x` is a modular line of `𝒜'`. Projection along `ℓ_x` makes `M(𝒜') → M(𝒜_x)/ℓ_x` a fibre bundle with
  fibre `ℂ` minus 3 points. So `Q := π_1M(𝒜') = F ⋊ P_X`.
- `P_X` acts on `F` through `ρ^X_Z : P_X → P_Z`, so `[N, F] = 1` in `Q`.
- Hence in `Q`, `α_1β_1α_2β_2α_3β_3 = (α_1α_2α_3)(β_1β_2β_3)`. So the hexagon relation holds in `Q` for
  **every** tuple satisfying the two product conditions. The image of the single-edge coset graph in `Q` is
  complete bipartite.
- The same holds for `π_1M(ℬ)`, a quotient of `Q`, for every `ℬ ⊆ 𝒜'`.

Consequently, any argument that uses the hexagon relation only through `π_1` of a sub-arrangement of
`𝒜_x ∪ 𝒜_y` proves only statements true of all normal-form tuples. That includes tuples that are not hexagons
in `Δ`. This kills the "use only the walls through `x̄` and `ȳ`" version of an `H_4` auxiliary arrangement: any
Huang-type arrangement must contain a wall outside `𝒜'`.

Calibration: in `H_3`, Huang's auxiliary arrangement I (10 walls) is `𝒜' ∪ 𝒜_V` for an `I_2(5)` point `V`. By
the check below, `V` is the intersection of a wall of `𝒜_y∖𝒜_z` and a wall of `𝒜_x∖𝒜_z`.

**(C) A fibred augmentation that sees the relation.** Let `V = w ∩ w'` be a codimension-2 flat of type `A_2`,
with `w ∈ 𝒜_y∖𝒜_z` and `w' ∈ 𝒜_x∖𝒜_z`. There are 9 such flats. Let `ℬ_V = 𝒜' ∪ 𝒜_V`, which is 19 walls, adding
the third wall through `V`. Then:
- `ℓ_x` is still modular in `ℬ_V`. The fibre is `ℂ` minus 4 points `p_1,p_2,p_3,p_4`. Here `p_4` comes from
  the new wall.
- `π_1M(ℬ_V) = F_4 ⋊_μ P_X`, and the monodromy `μ : P_X → P_4` lifts `ρ^X_Z` (forgetting `p_4`).
- `p_4` collides with `p_i` exactly along 3 walls of `𝒜_x∖𝒜_z`. So `μ(N)` is a **nontrivial** subgroup of
  the point-pushing group `F_3 = π_1(ℂ∖{p_1,p_2,p_3}, p_4) = ker(P_4 → P_3)`.
- The hexagon relation maps to the point-pushing identity
  `α_1 · Push_{λ_1}(α_2) · Push_{λ_1λ_2}(α_3) = 1` in `π_1(ℂ∖{p_1,…,p_4})`, with `λ_i = μ(β_i)` and `λ_1λ_2λ_3 = 1`.
- `[N, F] ≠ 1` in `π_1M(ℬ_V)`. The image of `F` is the free factor `⟨x_1,x_2,x_3⟩`, and a nontrivial pure
  braid cannot fix it together with the boundary word. So the identity is not automatic: for example
  `(a, a^{-1}, 1; n, n^{-1}, 1)` violates it for suitable `a ∈ F` and `n ∈ N`. Such tuples satisfy both product
  conditions but are not hexagons, and by (B) `𝒜'` cannot detect them.

Three `I_2(5)` flats also stay fibred, with 21 walls, fibre `ℂ` minus 6 points, and 7 collision walls outside
`𝒜_z`. So the single-edge case has a nontrivial shadow in a free-by-(pure `H_3`) group. That shadow is the
`H_4` substitute for the linear graph of groups of arXiv:2405.12068 §6.1.

Proof: `h4-case1-pure-normal-form-and-fibred-obstruction-proof`. The arrangement facts are checked in
`experiments/h4-case1-fibred-quotient-2026-09-17/` (`fibred.py`, `augment.py` and logs; `H_3` is calibrated).
Lane w5-042, 2026-09-18, unreviewed.

## Attempts

- **Open follow-up** (w5-042). Find which conclusion the point-pushing identity forces about
  `(α_i, λ_i)`, with `α_i ∈ ⟨x_1,x_2,x_3⟩` and `λ_i ∈ μ(N) ⊆ F_3`. A Huang-type conclusion would be that it
  forces a centre `s_4^kA_Y` or `y_2`. Two ways to get there:
  - find a `μ(P_X)`-invariant free splitting of `F_4` and run the Gauss–Bonnet argument in its Bass–Serre tree;
  - compute `μ` on the 15 meridians of `P_X` (a finite free-group computation) and attack the identity
    directly.
