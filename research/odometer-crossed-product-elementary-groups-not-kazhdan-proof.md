---
rg: 2
id: odometer-crossed-product-elementary-groups-not-kazhdan-proof
kind: route
title: Level subrings exhaust the odometer ring properly, level-K permutation models are exact, and a non-finitely-generated countable group has no (T)
target: odometer-crossed-product-elementary-groups-not-kazhdan
requires: []
artifacts:
  - research/artifacts/un-calibration-table-2026-09-13-part1.md
  - research/artifacts/un-calibration-table-2026-09-13-part2.md
---

The full argument is row 6 of `research/artifacts/un-calibration-table-2026-09-13-part2.md`, using Lemmas L1, L2, L4 and L7 of part 1.

1. **Level subrings.** `S_M` is the set of sums `Σ f_j u^j` with each `f_j` constant on the cosets of `2^M Z_2`.
   - It is a unital subring: `u f u^(-1) = f∘T^(-1)` is again constant on these cosets, and so are products.
   - `R = ∪_M S_M`.
   - `χ_(2^(M+1) Z_2) ∉ S_M`, by uniqueness of the normal form.
   
   Any finite subset lies in some `S_M`, so `R` is not finitely generated.
2. **Simplicity.** The Pestov artifact's §1.3 argument uses only `T^j x != x` (`j != 0`) and minimality. Both hold, since `x + j != x`
   and each orbit `x + Z` is dense in `Z_2`.
3. **Exact models.** For `K >= M`, `S_M` acts on `F_q^(Z/2^K)` by `f δ_c = f(c) δ_c` and `u δ_c = δ_(c+1)`. This is a ring homomorphism,
   because the pullback along `Z/2^K → Z/2^M` is equivariant.
   - Put `ρ = [ρ_K]_K`, with `ρ_K(x) = 0` for `K` below the level of `x`. It is a unital ring homomorphism into `∏_ω M_(2^K)(F_q)`.
   - It is injective: for `0 != Σ_(|j|<=d) f_j u^j`, the vectors `δ_(c+j)` are distinct once `2^K > 2d`.

   Stable finiteness and a faithful rank function follow from L1 and L2.
4. **Groups.**
   - `EL_n(R) = ∪_M EL_n(S_M)` is strictly increasing, since `e_12(χ_(2^(M+1) Z_2)) ∉ M_n(S_M)`. So it is not finitely generated.
   - A countable group with (T) is finitely generated (non-MF paper l.1173–1175, citing BHV Theorem 1.3.1), so `EL_n(R)` has no (T).
   - By L4, `EL_n(R) ⊆ GL_n(R)` embeds in `∏_ω GL_(n 2^K)(F_q)`, so it is LEF. LEF groups are MF and sofic, by L4.
