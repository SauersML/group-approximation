---
rg: 2
id: clifford-witness-has-no-hyperfinite-marked-representation-proof
kind: route
title: Marked lamps generate a UHF algebra, site permutations are outer on its trace completion, then the covariant obstruction lemma
target: clifford-witness-has-no-hyperfinite-marked-representation
requires: [hyperfinite-covariant-obstruction-lemma]
artifacts:
  - research/artifacts/stw99-x2-unitary-subgroup-reduction-2026-08-30.md
---

Let `ρ : Γ → U(W)` with `Γ = Λ ⋊ Σ` one of the two groups, `W` finite
injective with faithful normal trace `τ_W`, and suppose `ρ(ζ) ≠ 1`.  Since
`ζ` is a central involution, `p = ½(1 − ρ(ζ))` is a nonzero projection
central in `ρ(Γ)''`; compressing to `p W p` (again finite and injective)
we may assume `ρ(ζ) = −1`.

**Step 1: the marked lamp algebra is UHF.**  For `W`: the lamps satisfy
`c_ξ^2 = 1`, `c_ξ c_η = ζ c_η c_ξ` for `ξ ≠ η`, so with `ζ ↦ −1` the
C\*-algebra `A = C*(ρ(Λ))` is a quotient of the CAR/Clifford algebra
`Cl(ℓ^2(X)) ≅ M_{2^∞}`, which is simple, so `A ≅ M_{2^∞}`.  For `E_⊗`: the
lamps of one block generate the Clifford algebra on eight generators,
`Cl_8 ≅ M_16`, lamps in distinct blocks commute, so `A` is a quotient of
`⊗_{β ∈ Σ/K} M_16 ≅ M_{16^∞}`, simple, so `A ≅ M_{16^∞}`.

**Step 2: the lamp closure is R with the product trace.**  `τ_W|_A` is a
tracial state on a UHF algebra, hence the unique trace `tr`; `M = ρ(Λ)''`
is the completion of `A` under `τ_W`, so `M ≅ R` with `τ_W|_M = tr`.

**Step 3: every `g ∈ Σ \ {e}` moves infinitely many sites, resp. blocks.**
Write `g = t_a m τ^k` with `a ∈ Z[1/2]^3`, `m ∈ SL_3(Z)`, `k ∈ Z`.  For a
translation `t_v`, `t_v^{-1} g t_v = t_{a − v + m(2^k v)} m τ^k`, which lies
in `B` (resp. `K = τ^{-1}Bτ`) only if `k = 0` and
`(m − 1)v ∈ Z^3 − a` (resp. `(1/2)Z^3 − a`).  If `m ≠ 1`, the map
`v ↦ (m − 1)v` on `Z[1/2]^3 / Z^3 ≅ (Z(2^∞))^3` has infinite image, so the
solution set has infinite complement and `g` moves infinitely many cosets
`t_v B`.  If `m = 1`, `k = 0`, `g = t_a` with `a ≠ 0`: for `σ = τ^n t_v`,
`σ^{-1} t_a σ = t_{2^{-n} a} ∉ B` once `2^{-n} a ∉ Z^3`, and the cosets
`τ^n t_v B` for varying `v` are infinitely many.  If `k ≠ 0` then
`σ^{-1} g σ ∉ T ⊇ B` for every `σ`, so `g` moves every site.  The same
computation with `K` in place of `B` handles blocks.

**Step 4: `α_g` is outer on `R` for `g ≠ e`.**  Suppose `Ad u = α_g` with
`u ∈ R`.  Choose a unitary `u_0` in the finite Clifford (resp. finite tensor)
subalgebra over a finite set `F` of sites (resp. blocks) with
`‖u − u_0‖_2 < 1/4`.  By Step 3 pick two sites `ξ, η ∉ F` with
`gξ, gη ∉ F ∪ {ξ, η}` and put `x = ρ(c_ξ c_η)` (an even element, so it
commutes with the Clifford algebra over `F`; in the block case take `x` a
traceless unitary in one block outside `F` moved by `g`).  Then
`u_0 x u_0^* = x`, `tr(x) = 0`, and `x`, `α_g(x)` are traceless unitaries
in "disjoint" positions, so `‖x − α_g(x)‖_2 = √2`.  But
`‖α_g(x) − x‖_2 = ‖u x u^* − u_0 x u_0^*‖_2 ≤ 2‖u − u_0‖_2 < 1/2`, a
contradiction.  `R` is a factor, so outer means properly outer.

**Step 5: conclude.**  `hyperfinite-covariant-obstruction-lemma` applied to
`ρ : Λ ⋊ Σ → U(W)` gives that `Σ` is amenable.  But `Σ ⊇ SL_3(Z)` is not
amenable.  So `ρ(ζ) = 1`.
