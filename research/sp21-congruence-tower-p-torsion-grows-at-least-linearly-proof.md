---
rg: 2
id: sp21-congruence-tower-p-torsion-grows-at-least-linearly-proof
kind: route
title: Abelianize the completion of each congruence level, compare with the congruence group, and bound its abelianization by the lower p-series
target: sp21-congruence-tower-p-torsion-grows-at-least-linearly
requires: []
artifacts:
  - research/artifacts/sp21-torsion-growth-certificate-shape-2026-09-12.md
---

**Imported inputs.**
- **(DDMS)** For uniform `U` of dimension `D`, the lower p-series is
  `P_(i+1)(U) = U^(p^i)`, with `|P_i : P_(i+1)| = p^D` (also Ardakov–Brown
  arXiv:math/0511345 §2, read from the PDF). For any pro-p group,
  `[P_i, P_j] <= P_(i+j)`.
- **(C)** The pro-p completion of a normal subgroup of p-power index is its
  closure in the completion.
- **(T)** Finite-index subgroups of `Γ` have finite abelianization.

**Proof.**
1. **Translation.** `Δ_m` is normal of p-power index in `Δ`, with completion `P_m`.
   By (T), `H_1(Δ_m;Z)` is finite, so its p-part is `P_m^ab`.
2. **Upper bound.** The sequence `N/closure[N,P_m] -> P_m^ab -> U_m^ab -> 1` is
   exact, so `|U_m^ab| <= |P_m^ab| <= |U_m^ab|·|N/closure[N,P_m]|`.
3. **Lower bound.** `U_m = P_(m+1)(U)`, so
   `[U_m,U_m] <= P_(2m+2)(U) = U_(2m+1)`. Then `U_m^ab ->> U_m/U_(2m+1)`, of order
   `p^(D(m+1)) = p^D·p^(Dm) = p^D·[Δ:Δ_m]`.
4. **Derived series.**
   - The completion of `D_i` is `Φ^i(P)`, which maps onto `U_i`. So
     `|H_1(D_i;Z)_(p)| = |Φ^i(P)^ab| >= |U_i^ab| >= p^(D(i+1))`.
   - If `N` is finite, then `N ∩ Φ^i(P) = 1` for large `i`, so `Φ^i(P) ≅ U_i` and
     `[Δ:D_i] = [U:U_i]·|N|`. ∎
