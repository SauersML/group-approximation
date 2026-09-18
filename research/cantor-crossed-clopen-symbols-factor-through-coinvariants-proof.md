---
rg: 2
id: cantor-crossed-clopen-symbols-factor-through-coinvariants-proof
kind: route
title: Compute K_2(LC(X,Q)) as LC(X,Z) ⊗ K_2(Q) and use that inner automorphisms act trivially on K_2
target: cantor-crossed-clopen-symbols-factor-through-coinvariants
requires:
  - full-corners-must-kill-rational-k2-symbols
---

**Textbook inputs (not re-read).** (T1) `K_2` commutes with finite products of rings and with filtered
colimits of rings. (T2) An inner automorphism of a ring induces the identity on `K_2`. (T3) `K_2(Q)` is a
torsion group: it is `Z/2 ⊕ ⊕_(p odd) F_p^x` (Tate), as used in the statement of
`full-corners-must-kill-rational-k2-symbols`.

**Step 1.** `LC(X,Q)` is the filtered colimit, over finite clopen partitions `P` of `X`, of the unital
subrings `Q^P` of functions constant on the pieces. The transition maps are the diagonal maps. By (T1),
`K_2(LC(X,Q)) = colim_P K_2(Q)^P ≅ colim_P Z^P ⊗ K_2(Q) = LC(X,Z) ⊗ K_2(Q)`, with `(κ_p)_p ↦ Σ χ_p ⊗ κ_p`.
Symbols in a product ring are computed coordinatewise. So for units `a, b` constant on the pieces of `P`,
`{a,b} ↦ Σ_p χ_p ⊗ {a_p, b_p}`. In particular `{e_U(λ), e_U(μ)} ↦ χ_U ⊗ {λ,μ}`, and every element of
`K_2(LC(X,Q))` is a sum of such clopen symbols.

**Step 2.** The automorphism `φ ↦ φ ∘ γ^(-1)` of `LC(X,Q)` acts on `LC(X,Z) ⊗ K_2(Q)` by
`χ_U ⊗ κ ↦ χ_(γU) ⊗ κ`. Also `j ∘ (φ ↦ φ∘γ^(-1)) = c_γ ∘ j`, where `c_γ` is conjugation by `u_γ`, and
`c_γ` acts trivially on `K_2(R)` by (T2). So `j_* : LC(X,Z) ⊗ K_2(Q) -> K_2(R)` is constant on
`Γ`-orbits and factors through the coinvariants
`(LC(X,Z) ⊗ K_2(Q))_Γ = LC(X,Z)_Γ ⊗ K_2(Q) = D_X ⊗ K_2(Q)`, since `Γ` acts trivially on `K_2(Q)`. This
is `σ`, and part 1 follows from Step 1.

**Step 3 (part 2).** If `[χ_U] = m d` with `m κ = 0`, then `[χ_U] ⊗ κ = d ⊗ m κ = 0`. Every `κ` has
finite order by (T3).

**Step 4 (part 3).** `π^*` is injective since `π` is onto, which gives
`0 -> LC(K,Z) -> LC(X,Z) -> Q_X -> 0`. Coinvariants are right exact, so
`H_0(Γ; LC(K,Z)) -> D_X -> H_0(Γ; Q_X) -> 0` is exact.
- `H_0(Γ; LC(K,Z)) = colim_n H_0(Γ; Z[Γ/Γ_n])`.
- Each `H_0(Γ; Z[Γ/Γ_n])` is `Z`, via the augmentation, and the transition maps are multiplication by
  `[Γ_n : Γ_(n+1)]`.
- So `H_0(Γ; LC(K,Z)) ≅ ∪_n [Γ : Γ_n]^(-1) Z ⊆ Q`, which is divisible when every `m` divides some index.
  Apply the hypothesis to `m [Γ : Γ_n]`.

Its image `Δ ⊆ D_X` is therefore divisible, and `Δ ⊗ K_2(Q) = 0` by Step 3. Tensoring the exact sequence
with `K_2(Q)` gives `D_X ⊗ K_2(Q) ≅ H_0(Γ; Q_X) ⊗ K_2(Q)`. A pulled-back `U` has `[χ_U] ∈ Δ`.

**Step 5 (part 4).** For `N` a multiple of `m^2`, `v_p |SL_3(Z/N)| >= 8(v_p(N) - 1) + 3 >= v_p(m)` for
every `p | m`, since `|SL_3(Z/p^k)| = p^(8(k-1)) |SL_3(F_p)|` and `p^3` divides `|SL_3(F_p)|`. Taking
`N = (n+1)!` large, every `m` divides `[Γ : Γ((n+1)!)]`. The corner statement holds because the corner
map at `e = χ_U`, `q ↦ q e`, sends `{λ,μ}` to `s_U(λ,μ)`. ∎
