---
rg: 2
id: period-doubling-subshift-algebra-self-similarity-proof
kind: route
title: Odometer matrix units plus the decimation conjugacy identify the even-phase corner with the whole algebra
target: period-doubling-subshift-algebra-is-its-own-matrix-ring
requires: []
artifacts:
  - research/artifacts/period-doubling-elementary-group-phase-extraction-2026-09-12.md
---

The complete argument is Sections 1 to 5 of the artifact.

1. **Phases.** Every `x in X` has a unique residue `a_j(x) in Z/2^j` with
   `x(i) = nu_2(a_j(x) + i) mod 2` off the class `-a_j(x) mod 2^j`. It is locally constant and
   `a_j(Tx) = a_j(x) + 1`, so the phase sets `P_(j,a)` are clopen and permuted cyclically by `T`.
2. **Matrix units.** `E_ab = chi_(P_(j,a)) u^(a-b)` satisfy `E_ab E_cd = delta_bc E_ad` and
   `sum_a E_aa = 1`. So `A ≅ M_(2^j)(E_00 A E_00)`.
3. **Corner.** For `e = chi_(P_(1,0))`, `e f u^n e = 0` for odd `n`, so `eAe` is the algebraic
   crossed product of `(P_(1,0), T^2)`.
4. **Decimation.** On `P_(1,0)` the odd coordinates vanish. `D(x)(i) = 1 + x(2i)` is continuous,
   injective and intertwines `T^2` with `T`. It sends `T^m z` (`m` even) to `T^(m/2) z'`, where `z'`
   is `z` with centre `1`. `z'` is the limit of `T^(2^k) z` along odd `k`, so `z' in X`, and by
   minimality `D` is onto `X`. So `eAe ≅ A`.
5. **Conclusion.** `A ≅ M_2(eAe) ≅ M_2(A)`. Iterate, and use `EL_3(M_2(R)) = EL_6(R)`: block
   elementary matrices are elementary, and same-block elementary matrices are commutators
   `[e_ik(r), e_kj(1)]` through another block.
