---
rg: 2
id: injective-char-p-lamp-realizations-miss-fixed-points-proof
kind: route
title: "Injectivity transports finite order and fixed sets; torsion fixed sets in nV are clopen; nontrivial torsion automorphisms of the dual have nowhere-dense fixed cosets"
target: injective-char-p-lamp-realizations-miss-fixed-points
requires:
  - brin-thompson-torsion-has-clopen-fixed-sets
---

Notation as in the target. The only input is item 2 of `brin-thompson-torsion-has-clopen-fixed-sets`:
if `g ∈ nV` has finite order, then `Fix(g)` is clopen.

**Two facts about `C^n`.** It is perfect, so a clopen set with at most one point is empty. A clopen
set with empty interior is empty.

## Lemma F (fixed cosets are nowhere dense)

Let `1 ≠ γ ∈ GL_2(R)` and let `A` be its dual action on `M^`. Then `Ker(A − 1)` has empty
interior in `M^`. Hence every fixed set of an affine map `ξ ↦ Aξ + v` is empty or a coset of
`Ker(A − 1)`, and in either case has empty interior.

*Proof.*
- `Ker(A − 1) = {χ : χ∘γ^-1 = χ} = Ann(W)`, where `W = (γ^-1 − 1)M`.
- `W` is a nonzero `R`-submodule of `R^2`, since `γ^-1 − 1` is a nonzero `R`-linear map. So `W`
  contains `R·m ≅ R` for some `m ≠ 0`, because `R` is a domain. So `W` is infinite.
- Suppose `Ann(W)` had interior. It is a subgroup, so it would be open, and then it contains a
  basic neighbourhood of `0`, namely `Ann(F)` for some finite `F ⊆ M`.
- Then `W ⊆ Ann(Ann(W)) ⊆ Ann(Ann(F)) = ⟨F⟩`, which is finite. (Pontryagin duality for the
  discrete group `M`, where `Ann(Ann(S)) = ⟨S⟩`.) This contradicts `W` being infinite.
- The fixed set of `ξ ↦ Aξ + v` is `{ξ : (A − 1)ξ = −v}`, which is empty or a coset of
  `Ker(A − 1)`. ∎

## (0) Transport

- If `a_λ^N = id`, then `φ∘λ^N = a_λ^N∘φ = φ`. So `λ^N = id`, because `φ` is injective.
- For any `λ`: `λx = x` iff `φ(λx) = φ(x)` (injectivity) iff `a_λ(φ(x)) = φ(x)`. So
  `Fix(λ) = φ^-1(Fix a_λ)`.
- If `a_λ` has finite order, then `λ` is torsion, so `Fix(λ)` is clopen by the input.

## (i) Torus, `p ≥ 3`

- `d_c ∈ SL_2(F_p) = EL_2(F_p) ⊆ EL_2(R) ⊆ q(Λ)`, so some `λ` has `q(λ) = d_c`.
- The dual of `d_c` is `D = (d_c^-1)^T`, i.e. `D(α, β) = (c^-1 α, c β)`.
- `D − 1` multiplies the two coordinates by the nonzero scalars `c^-1 − 1` and `c − 1`, since
  `c ≠ 1` when `p ≥ 3`. So it is invertible, and `a_λ(ξ) = Dξ + v` has exactly one fixed point
  `ξ_c = −(D − 1)^-1 v`.
- `a_λ^j(ξ) = D^j ξ + (1 + D + ... + D^(j−1)) v`. For `j = p − 1`, `D^(p−1) = 1` and
  `Σ_(i<p−1) D^i = (D^(p−1) − 1)(D − 1)^-1 = 0`. So `a_λ^(p−1) = id`.
- By (0), `Fix(λ) = φ^-1(ξ_c)` is clopen and has at most one point, so it is empty. Hence
  `ξ_c ∉ Y`.
- If every `v_λ = 0`, then `ξ_c = 0`.

## (ii) Shears, every `p`

- Write `a_1(α, β) = (α + v', β − α + v'')` for the lift of `λ_1`, where `q(λ_1) = e_12(1)`, and
  `a_2(α, β) = (α − β + w', β + w'')` for the lift of `λ_2`, where `q(λ_2) = e_21(1)`.
- **Orders.** Let `U(α, β) = (α, β − α)`. Then `U^i(α, β) = (α, β − iα)`, and
  `a_1^i(ξ) = U^i ξ + Σ_(j<i) U^j v`.
  - For odd `p`: `Σ_(j<p) U^j v = (p v', p v'' − (p(p−1)/2) v') = 0`, so `a_1^p = id`.
  - For `p = 2`: `a_1^2(ξ) = ξ + (0, v')`, so `a_1` has order `2` (if `v' = 0`) or `4`.
  - The same holds for `a_2`. Hence `λ_1` and `λ_2` are torsion by (0).
- **Fixed sets.** `a_1(ξ) = ξ` iff `v' = 0` and `α = v''`. `a_2(ξ) = ξ` iff `w'' = 0` and
  `β = w'`. So `Fix a_1 ∩ Fix a_2 ⊆ {(v'', w')}`.
- `Fix(λ_1) ∩ Fix(λ_2) = φ^-1(Fix a_1 ∩ Fix a_2)` is clopen by (0) and has at most one point, so
  it is empty.
- In the linear case `v = w = 0`, and `0 ∈ Fix a_1 ∩ Fix a_2`. So `0 ∉ Y`.

## (iii) Conjugacies

Let `φ` be a homeomorphism onto `M^`.
- **Torsion.** Let `λ` have finite order with `q(λ) ≠ 1`. Then `Fix(λ)` is clopen, and it equals
  `φ^-1(Fix a_λ)`. `Fix a_λ` has empty interior by Lemma F, so its preimage under the homeomorphism
  `φ` has empty interior. So `Fix(λ)` is empty.
- **Shear lifts.** Let `q(λ) = e_12(r)` with `r ≠ 0`, and `a_λ(α, β) = (α + v', β − r(σ)α + v'')`.
  - `r(σ) : F_p^Z → F_p^Z` is surjective. Write `r = Σ_(j0 ≤ j ≤ j1) r_j t^j` with
    `r_j0, r_j1 ≠ 0`. Then `r(σ)α = v''` is a recurrence of order `j1 − j0` whose extreme
    coefficients are invertible, so it can be solved outward from any initial window.
  - Suppose `v' = 0`. Then `Fix a_λ = {r(σ)α = v''}` is nonempty. For `p = 2`,
    `a_λ^2(ξ) = ξ + (0, r(σ)v') = ξ`. For odd `p`, `a_λ^p = id` as in (ii). So `λ` is torsion
    with `q(λ) ≠ 1` and a fixed point, which contradicts the torsion bullet.
  - So `v' ≠ 0`. Then `a_λ` has no fixed point, and neither does `λ`.
  - `e_21(r)` is symmetric.
- For `p ≥ 3`, surjectivity is already excluded by (i).

## Checks

`check_affine_unipotent` and `check_affine_torus` in
`experiments/nv-break-2026-09-17/check_char_p_burger_lamp.py` compute these orders and fixed-point
counts exhaustively on the truncations `(F_p^2)^n` (radius-0 maps, so truncation is exact). The
unipotent orders are `{2: 4, 3: 3, 5: 5}`. The torus maps have order `p − 1` and exactly one fixed
point for `p = 3, 5, 7`.
