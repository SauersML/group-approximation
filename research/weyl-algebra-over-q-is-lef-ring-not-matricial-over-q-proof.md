---
rg: 2
id: weyl-algebra-over-q-is-lef-ring-not-matricial-over-q-proof
kind: route
title: Trace kills characteristic-zero models, reduction mod p onto the restricted Weyl representation gives exact models over F_p, and denominators block finite generation
target: weyl-algebra-over-q-is-lef-ring-not-matricial-over-q
requires: []
artifacts:
  - research/artifacts/un-calibration-table-2026-09-13-part1.md
  - research/artifacts/un-calibration-table-2026-09-13-part2.md
---

The full argument is rows 12–13 of `research/artifacts/un-calibration-table-2026-09-13-part2.md`, with Lemmas L1, L2, L4 and L7 of
part 1. It uses the standard PBW normal form `Σ c_ij x^i y^j` (recalled).

1. **Simple, domain.**
   - `ad_y(x^i) = −i x^(i−1)` and `ad_x(y^j) = j y^(j−1)`. In characteristic 0, iterating these from a nonzero element of an ideal
     reaches a nonzero scalar, so the ideal is `A`.
   - Leading terms multiply, so `A` is a domain.
2. **No characteristic-0 models.** If `ρ(x)ρ(y) − ρ(y)ρ(x) = ρ(1) = I_N`, the trace gives `0 = N` in `k`, which is impossible in
   characteristic 0.
3. **Models over `F_p`.**
   - On `V = F_p[x]/(x^p)`, `x ↦ x` and `y ↦ −d/dx` satisfy the relation, so `A_1(Z_(p)) → End(V)` is a ring homomorphism.
   - `{x^i (d/dx)^j : i, j < p}` is linearly independent. Take the least `j_0` with a nonzero coefficient and apply the sum to
     `x^(j_0)`: this gives `Σ_i c_(i j_0) j_0! x^i = 0` with `i < p`, which is impossible.
   - Each finite subset of `A` lies in `A_1(Z_(p))` for all but finitely many `p`, and a nonzero element maps to a nonzero matrix
     once `p` exceeds its degrees and does not divide some nonzero coefficient.
   - So `ρ = [ρ_p]` is a unital injective ring homomorphism into `∏_ω M_p(F_p)`. L1 gives stable finiteness and a rank function, and
     L2 (simplicity) makes it faithful.
4. **Groups.**
   - By L4, `EL_n(A)` embeds in `∏_ω GL_(np)(F_p)`, so it is LEF, MF and sofic.
   - Finitely many elements have coefficients in `Z[1/m]` for some `m`. So `A` is not finitely generated, and
     `EL_n(A) = ∪_m EL_n(A_1(Z[1/m]))` is strictly increasing, since `e_12(1/p) ∉ M_n(A_1(Z[1/m]))` for `p ∤ m`.
   - By L7 (non-MF paper l.1173–1175, citing BHV Theorem 1.3.1), a countable group with (T) is finitely generated, so `EL_n(A)` has no (T).
