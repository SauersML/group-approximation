---
rg: 2
id: window-defect-forces-module-triple-inexactness-proof
kind: route
title: Functional calculus on the boundary gap, and vanishing of ideal elements on boundary-like windows
target: window-defect-forces-module-triple-inexactness
requires: []
---

1. **`f(D)` dies on `Z`.**
   - The representations `pi_zeta`, `zeta ∈ Z`, together are faithful on `C(Z) ⋊_r G`.
   - By (H1), `spec(pi_zeta(q D)) ∩ (-eps, eps) = ∅` for all `zeta`. Hence the spectrum of
     `q(D)` misses `(-eps, eps)` and `f(q D) = 0`.
   - So `q(f(D)) = f(q D) = 0`.
2. **`f(D)` acts almost as the identity on `eta_n`.**
   - Fix `delta > 0` and choose a polynomial `p` with `|p - f| < delta` on
     `[-||D||, ||D||]`. Then `||f(D) - p(D)|| < delta` and `|p(0) - 1| < delta`.
   - Writing `p(t) = sum_k c_k t^k`,
     `||pi_(xi_n)(p(D)) eta_n - p(0) eta_n|| <= sum_(k>=1) |c_k| ||D||^(k-1) ||pi_(xi_n)(D) eta_n||`,
     which tends to `0` by (H2)(a).
   - Hence `limsup ||pi_(xi_n)(f(D)) eta_n - eta_n|| <= 2 delta` for every `delta`.
3. **Ideal elements vanish on `eta_n`.** Take `i = sum_(g ∈ T') b_g u_g` with `T'` finite and
   `b_g ∈ C_0(U)`.
   - `(pi_xi(b_g u_g) eta)(k) = b_g(k^-1 xi) eta(g^-1 k)`, which is supported on `k ∈ g R_n`.
   - For large `n`, `T' ⊆ S_n`, so `k ∈ S_n R_n` and `k^-1 xi_n ∈ N_n` by (H2)(b).
   - Each `b_g` is continuous and vanishes on `Z`, so `sup_(N_n) |b_g| -> 0`.
   - Hence `||pi_(xi_n)(i) eta_n|| <= sum_g sup_(N_n) |b_g| -> 0`.
   - Such `i` are dense in `C_0(U) ⋊_r G`, and `pi_xi` is contractive. So
     `||pi_(xi_n)(i) eta_n|| -> 0` for every `i` in the ideal.
4. **Distance.** For `i` in the ideal,
   `||f(D) - i|| >= limsup ||pi_(xi_n)(f(D) - i) eta_n|| >= 1`, by steps 2 and 3. Since
   `||f(D)|| <= 1`, the distance is exactly `1`.
5. **Trivial-model check.**
   - Suppose `Z = {zeta}` is a fixed point.
   - (H2)(b) makes the coefficients `a_g(k^-1 xi_n)` uniformly close to `a_g(zeta)` on `T R_n`.
   - So `||pi_(xi_n)(D) eta_n - pi_zeta(D) eta_n|| <= sum_g sup_(N_n) |a_g - a_g(zeta)| -> 0`.
   - With (a) this forces `0 ∈ spec(pi_zeta(D))`, against (H1).
