---
rg: 2
id: transvection-normal-generation-recovers-invariant-measures-proof
kind: route
title: Rank lengths give the lower bound; Kakutani–Rokhlin towers with uniform visit ratios, level permutations and Whitehead diagonals give the upper bound
target: transvection-normal-generation-recovers-invariant-measures
requires: [subshift-el-rank-lengths-force-non-uniform-simplicity]
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
---

The full proof is Theorem B in part 1, §2.

- **Lower bound.** By the required claim, `ℓ_μ(e_12(χ_U)) = μ(U)` and `ℓ_μ(e_12(χ_V)) = μ(V)`, and `ℓ_μ` is subadditive and conjugation-invariant.
- **Uniform ratios.** For `δ > 0` there is `L` such that along every orbit segment of length `≥ L`, the ratio of visits to `U` and to `V` lies in `[ρ_min − δ, ρ_max + δ]`. Proof: weak* limits of empirical measures are invariant, and `inf_μ μ(V) > 0`.
- **Towers.** Take a Kakutani–Rokhlin partition with heights `≥ L` whose levels each lie inside or outside `U`, and inside or outside `V` (Herman–Putnam–Skau). In tower `j` there are `a_j` levels in `U` and `b_j` levels in `V`, with `a_j/b_j ∈ [ρ_min−δ, ρ_max+δ]`.
  - Cut the `U`-levels into consecutive groups of `b_j` levels plus a remainder. This gives `U = ⊔_{t≤T} U_t`, with `T ≤ ⌊ρ_max⌋ + 1`.
  - For `t ≤ s` with `s ≥ ⌈ρ_min⌉ − 1`, every tower's group `t` is full.
- **Units.** A permutation `σ` of the levels of each tower that maps the first `|Γ_{j,t}|` levels of `V` onto group `t` gives `w_t = Σ u^{σ(i)−i} χ_{T^iB_j} ∈ R^×` (checked in the faithful orbit representation), with `w_t χ_{V′_t} w_t^{-1} = χ_{U_t}`.
  - `D_t = diag(w_t,w_t,w_t^{-2}) = diag(w_t,w_t^{-1},1)·diag(1,w_t^2,w_t^{-2}) ∈ G` by the characteristic-2 Whitehead identity `e_12(c)e_21(c^{-1})e_12(c)e_12(1)e_21(1)e_12(1) = diag(c,c^{-1},1)`.
  - `D_t e_12(χ_{V′_t}) D_t^{-1} = e_12(χ_{U_t})`.
- **Count.**
  - Full groups: `V′_t = V`, one conjugate.
  - Partial groups: `e_12(χ_{V′}) = [e_13(χ_{V′}), e_32(χ_V)]`, and `e_32(χ_V) = P e_12(χ_V) P^{-1}` with `P = P_(13) ∈ SL_3(F_2)`. Two conjugates.
  - Total: `ν ≤ s + 2(T − s) ≤ 2⌊ρ_max⌋ − ⌈ρ_min⌉ + 3`.
- **Recovery.** Numerator `μ(U)/μ(V_n) + O(1)`, denominator `1/μ(V_n) + O(1)`.
- **Model test.** For the 2-adic odometer with `V` a level-`n` cylinder and `U = X`, the 2^n translates of `V` give `ν = 2^n ∈ [2^n, 2^n + 3]`.
