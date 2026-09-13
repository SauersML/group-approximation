---
rg: 2
id: toeplitz-defect-ideal-connected-iff-extension-k1-injective-proof
kind: route
title: J + T_2 is an extension of O_2 by J; apply the quotient lifting lemma
target: toeplitz-defect-ideal-connected-iff-extension-k1-injective
requires: [o2-quotient-extension-ideal-k1-injective-iff-algebra, k1-injectivity-extends-over-properly-infinite-quotients]
artifacts:
  - research/artifacts/k1-defect-ideal-o2-quotient-lifting-2026-09-13.md
---

The full derivation is in artifact section 3.

1. **Structure of `B_J`.**
   - `B_J` is the preimage of the C\*-algebra `q_J(iota_1(T_2))` under `q_J: A_T -> A_T/J`, so it is
     closed. It is properly infinite because it contains `iota_1(s_1), iota_1(s_2)`.
   - `B_J/J ≅ T_2/iota_1^{-1}(J)`. That ideal contains `p_3`, hence K, and does not contain 1: the
     map `A_T -> O_2 * T_2` kills e.
   - Every nonzero ideal of `T_2` contains the essential simple ideal K, and `T_2/K ≅ O_2` is simple.
     So the ideal is K, and `B_J/J ≅ O_2`.
2. **K-theory.** `K_*(J) = (Z,0)` is computed in route `lxi-from-halving-and-toeplitz-defect-ideal`
   from Blanchard 0804.4624v13 Lemma 4.4 and Germain's sequence. By
   `o2-quotient-extension-ideal-k1-injective-iff-algebra` (b), `K_*(B_J) ≅ K_*(J)`.
3. **Items 2 and 3.** Item 2 is part (d) of that claim. For item 3, `B_J` is unital and properly
   infinite, so LXI makes it K1-injective.
4. **Item 4.** (⟸) is route `lxi-from-halving-and-toeplitz-defect-ideal`. (⟹) uses route
   `o2-free-circle-halving-homotopy-from-lxi` and item 3.
5. **Item 5.** The unital surjection `A_T -> O_3` with `iota_1(s_1), iota_1(s_2), iota_2(s_1),
   iota_2(s_2) -> r_1, r_2, r_3, r_2` sends e to `r_3r_3^* ≠ 0`, so J maps onto the simple algebra O_3.
   - The map extends to a unital `M(J) -> M(O_3) = O_3`, since `ker π` is invariant under `M(J)`.
   - A unital O_2 there would give `[1] = 2[1]` in `K_0(O_3) = Z/2`, but `[1] ≠ 0`.
6. **I_f.** `A_T -> O_2` is unital and surjective, and `K_1(A_T) = 0`. So `U(I_f~)` is connected iff
   `A_T` is K1-injective. The forward implication `A_T` K1-injective ⟹ LXI is Blanchard Proposition 4.2,
   (i) => (v). The converse holds because `A_T` is properly infinite.
