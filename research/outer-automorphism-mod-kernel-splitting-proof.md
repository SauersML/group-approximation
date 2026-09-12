---
rg: 2
id: outer-automorphism-mod-kernel-splitting-proof
kind: route
title: A splitting makes the conjugation inner, and transpose-inverse is not inner on SL_3(Z)
target: outer-automorphism-mod-kernel-refutes-centralizer-splitting
requires: []
---

Elementary, and self-contained in the claim body. The steps:

1. **Splitting forces inner.** `c` centralizes `sigma(Gamma)`, so
   `sigma(z) sigma(gamma) sigma(z)^-1 = sigma(m_0) sigma(gamma) sigma(m_0)^-1`.
   Injectivity gives `z gamma z^-1 = m_0 gamma m_0^-1`.
2. **Hypotheses of the premise.** In `P = SL_3(Z) ⋊ <alpha>`:
   - `SL_3(Z)` is Kazhdan (Kazhdan; Bekka--de la Harpe--Valette, Theorem 1.6.1)
     and normal;
   - `P` is residually finite, hence sofic, since `SL_3(Z)` is linear and of
     index 2;
   - `[alpha, x] = alpha(x) x^-1` lies in `SL_3(Z)`.
3. **Not inner.** For a matrix with characteristic polynomial
   `t^3 - a t^2 + b t - 1`, `tr = a` and `tr(C^-1) = b`. With `a = 2` and `b = 0`,
   the companion matrix is in `SL_3(Z)`, and `tr(alpha(C)) = tr(C^-1) = 0 != 2`.
4. **Non-normal version.**
   - The Kun--Thom Theorem E pair is residually finite and Kazhdan, with
     `Gamma_KT` infranormal and not normal (`research/artifacts/kun-thom-2608-06222-verified.md`).
   - Products preserve residual finiteness and property (T).
   - The compression semigroup of `Gamma_KT x SL_3(Z)` contains
     `P_(Gamma_KT) x SL_3(Z)`, so it generates `G_KT x SL_3(Z)`.
   - Step 3 applies on the second coordinate. ∎
