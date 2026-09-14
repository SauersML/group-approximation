---
rg: 2
id: countable-lef-groups-embed-in-two-generator-lef-groups-proof
kind: route
title: Place Ore commutator data on power-of-two levels and isolate each generator by one fixed word in an ultraproduct
target: countable-lef-groups-embed-in-two-generator-lef-groups
requires: [ore-even-permutations-are-commutators]
artifacts:
  - research/artifacts/sk-universal-lef-host-b-2026-09-13.md
---

Artifact §1. Enumerate `Γ = {γ_1, γ_2, …}`, repeating elements if `Γ` is finite.

1. **Models.** Since `Γ` is LEF, there are finite groups `Q_k` and maps `φ_k : Γ -> Q_k` that are injective on
   `F_k = {1, γ_1,…,γ_k}` and satisfy `φ_k(gh) = φ_k(g)φ_k(h)` for `g,h ∈ F_k`. So for fixed `g,h`:
   - `φ_k(gh) = φ_k(g)φ_k(h)` for all large `k`;
   - `φ_k(g) ≠ 1` for all large `k` when `g ≠ 1`, since `φ_k(1) = 1` and `φ_k` is injective on `F_k`.
2. **Even permutations.** Let `π_k(g) ∈ Sym(Q_k × {1,2})` act by `(x,e) ↦ (φ_k(g)x, e)`. Its cycles come in pairs of
   equal length, so it is even. By `ore-even-permutations-are-commutators`, choose for `j ≤ k` permutations
   `α_(j,k), β_(j,k)` with `π_k(γ_j) = [α_(j,k), β_(j,k)]`, where `[x,y] = xyx^(-1)y^(-1)`.
3. **Levels.** Put `L_k = 4^(k+1)`, `X_k = Q_k × {1,2} × Z/L_k`, `p_j = 2^(2j-1)` and `q_j = 4^j`.
   - `b_k(x,i) = (x, i+1)`.
   - `a_k(x,i) = (τ_(k,i)(x), i)`, where `τ_(k,i)` is `α_(j,k)` if `i = p_j`, `β_(j,k)` if `i = q_j` (for `j ≤ k`),
     and the identity otherwise. The `2k` residues `p_j, q_j` are distinct because they are distinct powers of 2
     below `L_k`.
4. **Isolation.** `b_k^(-n) a_k b_k^n` sends `(x,i)` to `(τ_(k,i+n)(x), i)`. So for `j ≤ k` the fixed word `w_j(a,b)`
   acts on level `i` by `[τ_(k,i+p_j), τ_(k,i+q_j)]`.
   - This is trivial unless `i+p_j ≡ s'` and `i+q_j ≡ s` for some `s, s' ∈ P_k = {2^1,…,2^(2k)}`.
   - In that case `q_j − p_j ≡ s − s' (mod L_k)`. Both sides have absolute value below `4^k < L_k/2`, so
     `q_j − p_j = s − s'` in `Z`.
   - Positive differences of powers of 2 determine the pair: `2^c − 2^d = 2^(c') − 2^(d')` with `c > d`, `c' > d'`
     forces `d = d'` by 2-adic valuation, then `c = c'`. So `s = q_j`, `s' = p_j`, and `i ≡ 0`.
   - Hence `w_j(a_k,b_k)` acts by `π_k(γ_j)` on level 0 and trivially on every other level.
   - A small exhaustive check of this step on MSI passed (artifact §6).
5. **Ultraproduct.** Fix a nonprincipal ultrafilter `ω` and let `U = ∏_ω Sym(X_k)`, the algebraic ultraproduct. Let
   `ι_k(g)` act by `π_k(g)` on level 0 and trivially elsewhere, and put `ι(g) = [ι_k(g)]`.
   - By 1, `ι` is a homomorphism, and it is injective.
   - For each `j`, `ι(γ_j) = w_j(a,b)` with `a = [a_k]` and `b = [b_k]`, since equality holds for every `k ≥ j`.
   - So `ι(Γ) ≤ Δ := ⟨a,b⟩`.
6. **LEF.** Given finitely many elements of `U`, with finitely many products among them and finitely many
   inequalities, each condition holds for `ω`-almost every `k`. Finitely many conditions hold together at some `k`,
   which gives an injective partial homomorphism into `Sym(X_k)`. So every subgroup of `U` is LEF, including `Δ`.
7. If `Γ` is infinite, `Δ ⊇ ι(Γ)` is infinite. ∎
