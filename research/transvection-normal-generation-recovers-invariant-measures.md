---
rg: 2
id: transvection-normal-generation-recovers-invariant-measures
kind: claim
title: The number of conjugates of e_12(χ_V) needed to write e_12(χ_U) in EL_3(LC(X,F_2)⋊Z) lies between sup_μ μ(U)/μ(V) and 2⌊sup⌋ − ⌈inf⌉ + 3, so normal generation numbers recover the measure of a uniquely ergodic X
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
---

**Statement.** Let `(X,T)` be a minimal homeomorphism of an infinite Cantor set, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`. Let `U, V ⊆ X` be clopen with `V ≠ ∅`, and put `ρ_max = sup_μ μ(U)/μ(V)` and `ρ_min = inf_μ μ(U)/μ(V)` over `μ ∈ M_T(X)`. Let `ν` be the least number of conjugates of `e_12(χ_V)^{±1}` whose product is `e_12(χ_U)`. Then

`ρ_max ≤ ν ≤ 2⌊ρ_max⌋ − ⌈ρ_min⌉ + 3`.

- **Uniquely ergodic `X`, with `ρ = μ(U)/μ(V)`:** `⌈ρ⌉ ≤ ν ≤ ⌊ρ⌋ + 3`.
- **Recovery of the measure.** For clopen `V_n` with `μ(V_n) → 0`,
  `μ(U) = lim_n ν_{e_12(χ_{V_n})}(e_12(χ_U)) / ν_{e_12(χ_{V_n})}(e_12(1))`.

  So the invariant measure is read off from normal generation numbers in the group.

**Status: established** by `transvection-normal-generation-recovers-invariant-measures-proof`. UNREVIEWED; queued with sk-verify-13.

**Review (sk-verify-15, 2026-09-13): PASS, conditional.** Lower bound, uniform ratios, the δ-choice (s ≥ ⌈ρ_min⌉−1, T ≤ ⌊ρ_max⌋+1), level-permutation units, D_t ∈ G, the two-conjugate remainder step and recovery of μ re-derived. Conditional on the rank-function import of `cantor-z-crossed-product-embeds-in-continuous-factor` (no review line) and on Theorem A (line owned by sk-verify-14). See `research/artifacts/sk-verify-15-2026-09-13-part2.md` §3.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived: uniform visit ratios, the δ-choice bounds s ≥ ⌈ρ_min⌉−1 and T ≤ ⌊ρ_max⌋+1, level-permutation units, D_t ∈ G, the two-conjugate commutator step, and recovery. See `research/artifacts/sk-verify-16-2026-09-13.md` §4.
