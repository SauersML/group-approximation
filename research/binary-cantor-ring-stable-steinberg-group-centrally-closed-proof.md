---
rg: 2
id: binary-cantor-ring-stable-steinberg-group-centrally-closed-proof
kind: route
title: The Pimsner–Voiculescu terms around K_2 are LC(X,K_2(F_2)) = 0 and LC(X,K_1(F_2)) = 0; then Kervaire–Steinberg and Gersten
target: binary-cantor-ring-stable-steinberg-group-centrally-closed
requires:
  - abc-twisted-laurent-k-theory-fibration
  - quillen-k-theory-of-finite-fields
  - steinberg-group-homology-gives-k2-and-k3
  - minimal-cantor-crossed-product-k-theory-formula
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part1.md
---

- **K_2 = 0.** Put `A = LC(X,F_2)`.
  - `A` is regular supercoherent and `σ = (·)∘T^(−1)` is a unital automorphism, for ANY homeomorphism `T` (Steps 1–2 of `subshift-crossed-product-k0-is-coinvariant-group-proof`). So the ABC exact sequence gives `K_2(A) → K_2(R_X) → K_1(A)`.
  - K-theory commutes with filtered colimits, so `K_2(A) = LC(X, K_2(F_2)) = 0` and `K_1(A) = LC(X, F_2^×) = 0` (`quillen-k-theory-of-finite-fields`). Hence `K_2(R_X) = 0`.
- **Steinberg group.** `K_2(R) = ker(St(R) → E(R))` and `St(R) → E(R)` is onto. So `St(R_X) ≅ E(R_X)`. By `steinberg-group-homology-gives-k2-and-k3` (i), `H_2(E(R_X);Z) ≅ K_2(R_X) = 0`.
- **H_3.** By (iii) of the same node, `H_3(E(R_X);Z) = H_3(St(R_X);Z) ≅ K_3(R_X)`. For minimal `(X,T)`, `minimal-cantor-crossed-product-k-theory-formula` gives `K_3(R_X) ≅ K^0(X,T) ⊗ Z/3`. ∎
- **Model test.** One-point system: `R = F_2[t^(±1)]` and `K_2 = K_2(F_2) ⊕ K_1(F_2) = 0` (Bass–Heller–Swan) ✓. `E(F_2[t^(±1)]) = SL(F_2[t^(±1)])` is then centrally closed, consistent with the vanishing `K_2` ✓.
