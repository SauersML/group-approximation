---
rg: 2
id: ternary-cylinder-defect-descent-proof
kind: route
title: Bound disjoint defect products above by the cube-zero Frobenius bound and below by compressing along the anti-central sign idempotent of the next cylinder
target: ternary-cylinder-defect-products-descend-in-sign-sectors
requires:
  - ternary-anti-central-two-root-defect-has-a-uniform-gap
  - sylvester-rank-functions-compress-along-commuting-elements
  - simple-group-rank-functions-are-augmentation-or-detecting
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

Artifact Section 3, Theorem 3.1.

1. **Upper.** `N^B_12` commutes with `P_k` and has cube `0`, so `N(D_B P_k) <= N(N^B_12 P_k) <= (2/3) N(P_k)`.
2. **Lower.** `E = Q_B P_k` commutes with `F_3[iota_B(G)]`, because `iota_B(z)` is central in `iota_B(G)` and
   the cylinders are disjoint.
   * So `X -> N(F_3[iota_B](X) E)/N(E)` is a Sylvester rank function.
   * It is anti-central, since `F_3[iota_B](eps_-) = Q_B`.
   * Its defect is `N(D_B Q_B P_k)/h_k`, which is at least `c_3`.
3. **Sector half.**
   * On `Y = R_s P_k eps_-` with `pi(s) = +1`, `[tau_C] = [z] prod [tau_(A_i)]` acts by `-1`. So
     `Q_(C\B) Y = (1 - Q_B) Y`.
   * A unit `u` in `V` fixing the `A_i` and swapping `B` with `C \ B` commutes with `P_k`, `R_s` and `eps_-`, and
     conjugates `Q_B` to `Q_(C\B)`.
   * Conjugation invariance and splitting along the commuting idempotent `Q_B` give the two equal halves.
4. **Positivity.**
   * If `h_k = 0`, then by V-conjugation `N(Q_(Bw) P_k) = 0` for every nonempty proper prefix `w`.
   * Compressing along `P_k` through `iota_B` gives a rank function killing every `1 - [tau_w] = 2 Q_w`.
   * Its null normal subgroup contains `tau_w`, which is not in `<z>`. So it is `G`, and the function is the
     augmentation rank.
   * Hence `f(k+1) = f(k) · 0 = 0`. QED
