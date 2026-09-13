---
rg: 2
id: o2-quotient-extension-ideal-k1-injective-iff-algebra-proof
kind: route
title: Lift the quotient loop through exponentials; loops in U(O_2) are null by Jiang
target: o2-quotient-extension-ideal-k1-injective-iff-algebra
requires: [z-stable-unital-algebras-are-k1-bijective, k1-injectivity-extends-over-properly-infinite-quotients]
artifacts:
  - research/artifacts/k1-defect-ideal-o2-quotient-lifting-2026-09-13.md
---

The full derivation is in artifact sections 1 and 2.

1. **Loops in O_2.** Let `C = C(T, O_2)`, with evaluation `ev` at 1 and kernel `SO_2`.
   - C is unital and Z-stable, and `K_1(C) = K_1(O_2) ⊕ K_0(O_2) = 0`. So `U(C)` is connected by
     `z-stable-unital-algebras-are-k1-bijective` (Jiang, arXiv:math/9707228v1, Theorem 2, read in the PDF).
   - Take a path `w_s` from a based loop f to 1, and correct it to `w_s c(ev(w_s))^*`. This gives a
     path in `U(1 + SO_2)`, so `U((SO_2)~)` is connected.
   - Trust surface: `O_2 ⊗ Z ≅ O_2`.
2. **Lifting.** Let `u ∈ U(I~) ∩ U_0(B)` with `q(u) = 1`, and take a path `w` in `U(B)` from 1 to u.
   - `γ = q∘w` is a based loop, so by step 1 it is a product `exp(ih_1)⋯exp(ih_m)`, with
     `h_k = h_k^* ∈ (SO_2)~`.
   - Lift each `h_k` to a self-adjoint in `(SB)~` and put `ω = ∏ exp(ik_k)`. Then ω is a based loop
     in `U(B)` with `q∘ω = γ`. Its endpoint scalar μ satisfies `μ1 = γ_0 = 1`.
   - `ω_t^* w_t` is a path from 1 to u in `U(B) ∩ (1+I) ⊆ U(I~)`. This proves (a).
3. (b) is the six-term sequence with `K_*(O_2) = 0`.
4. (c)(⟸): `[u] = 0` in `K_1(I)` gives `[u] = 0` in `K_1(B)`, so `u ∈ U_0(B)`, and step 2 applies.
   (c)(⟹) is `k1-injectivity-extends-over-properly-infinite-quotients`, with the properly infinite,
   K1-injective quotient O_2 (Cuntz 1981).
5. (d): every unitary of `I~` has class in `K_1(I) ≅ K_1(B) = 0`.
6. **Z-stable quotients** (artifact `k1-defect-ideal-z-stable-quotients-2026-09-13`, Lemma 1' and
   Corollary 3').
   - If Q is unital and Z-stable with `K_0(Q) = 0`, then `C(T) ⊗ Q` is Z-stable. A based loop `f` has
     class in `K_1(SQ) ≅ K_0(Q) = 0`, so `f ∈ U_0(C(T) ⊗ Q)` by Jiang, and the constant correction of
     step 1 applies. So step 2 goes through.
   - `K_1(I) -> K_1(B)` is injective because `K_0(Q) = 0`.
   - (⟹) uses that Q is properly infinite and K1-injective by Jiang.
7. **Applications.** `O_2 ⊗ C(T)` is admissible.
   - For `J_c ⊆ O_2 * C(T)`, K1-injectivity of `J_c~` is equivalent to K1-injectivity of `O_2 * C(T)`,
     which is the halving homotopy.
   - For `I_c ⊆ T_2 * T_2`, `K_1(I_c) ≅ K_1(T_2 * T_2) = 0`, so connectivity of `U(I_c~)` is
     K1-injectivity of `T_2 * T_2`. That is LXI by Blanchard arXiv:0804.4624v13, Proposition 4.2
     (i) <=> (v), read in the PDF.
