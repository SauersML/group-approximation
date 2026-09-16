---
rg: 2
id: lef-graded-simple-base-sf-iff-rank-condition-proof
kind: route
title: Absorb a weakly finite image into its LEF group ring, and close the cycle with Malcolmson and Hahn-Banach
target: lef-graded-simple-base-sf-iff-rank-condition
requires:
  - lef-group-rings-over-stably-finite-rings-are-stably-finite
  - rank-condition-rings-have-weakly-finite-images
artifacts:
  - research/artifacts/deligne-twisted-sf-rank-condition-dichotomy-2026-09-16.md
---

Artifact Sections 1–2 (Lemma 1.1, Proposition 1.2, Theorem 2.1, Lemma 2.2).

## Why sufficient

`A != 0`, since `A_1` is simple.

1. **Absorption (Lemma 1.1).** For `phi : A -> R` unital, `Phi(Σ x_g) = Σ phi(x_g) g` is a unital ring
   homomorphism `A -> R[Gamma]`, since `x in A_g`, `y in A_h` give `xy in A_(gh)` and group labels commute
   with `R`. The labels are an `R`-basis, so `Phi` is injective iff `phi` is injective on every `A_g`.
2. **Injectivity on components (Proposition 1.2).** Let `R != 0`.
   - `ker phi ∩ A_1` is a proper ideal of the simple ring `A_1`, hence `0`.
   - If `x in A_g` and `phi(x) = 0`, then `x A_(g^-1) ⊂ A_1 ∩ ker phi = 0`.
   - `1 in A_(g^-1) A_g` by strong grading, so `x = 0`.
3. **2 => 1.** Let `R != 0` be a weakly finite image. By 1–2, `A` embeds unitally in `R[Gamma]`, which is
   stably finite by `lef-group-rings-over-stably-finite-rings-are-stably-finite`. `M_n(A)` is a unital
   subring of `M_n(R[Gamma])`, so `A` is stably finite.
4. **3 => 2.** This is `rank-condition-rings-have-weakly-finite-images`.
5. **1 => 3.** Pad `XY = I_(n+1)` to the square pair `[X | 0]` and `[[Y],[0]]`. Its reverse product
   `diag(YX, 0)` is not `I_(n+1)`.
6. **1 => 5.** Take `X_i Y_k = delta_ik` in `M_n(A)`. Direct finiteness gives `Y_1 X_1 = 1`, so
   `X_2 = X_2 Y_1 X_1 = 0`, contradicting `X_2 Y_2 = 1`.
7. **5 => 3.** Contrapositive.
   - If `A^(n+1)` is a retract of `A^n`, then adding identities makes `A^(n+k)` a retract of `A^(n+k-1)`.
   - Composing for `k = 1, ..., n` makes `A^(2n)` a retract of `A^n`.
   - Cutting the `2n x n` and `n x 2n` matrices into `n x n` blocks gives `X_i Y_k = delta_ik I_n`.
8. **3 <=> 4 (Lemma 2.2).**
   - A state kills retractions `A^n ≅ A^(n+1) ⊕ P`.
   - Conversely, the rank condition gives `-r[A] ∉ K_0(A)^+` for all `r >= 1`.
   - Then `p(x) = inf{m/k : kx <= m[A]}` is a sublinear functional with `p([A]) = 1` and `p(-[A]) = -1`,
     and `p <= 0` on `-K_0^+`.
   - Hahn–Banach over `Q` extends `q[A] -> q` below `p` on `K_0(A) ⊗ Q`. Its restriction is a state.

Steps 4–8 hold for every nonzero ring. The LEF and graded hypotheses enter only in step 3.
