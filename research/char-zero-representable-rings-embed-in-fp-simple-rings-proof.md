---
rg: 2
id: char-zero-representable-rings-embed-in-fp-simple-rings-proof
kind: route
title: Primary decomposition and Noether normalization put C in matrices over Q(t_1..t_k), which lies in R_k
target: char-zero-representable-rings-embed-in-fp-simple-rings
requires:
  - rational-function-fields-embed-in-fp-simple-rings
---

Lane proof, not independently reviewed. Write `F_k = Q(t_1..t_k)`.

## 1. Matrix rings over a finitely presented simple ring
If `R` is finitely presented and simple, so is `M_e(R)`.
- *Presentation.* Take the generators of `R` as scalar matrices `g·I`, together with
  matrix units `e_ij`. Impose the relators of `R`, the relations
  `e_ij e_kl = δ_jk e_il` and `Σ e_ii = 1`, and commutation of each generator of `R` with
  every `e_ij`. This presents `R ⊗_Z M_e(Z) = M_e(R)`.
- *Simplicity.* Every ideal of `M_e(R)` is `M_e(I)` for an ideal `I` of `R`.

## 2. Commutative algebra: C embeds in M_e(F_k)
**Lemma.** Every finitely generated commutative `Q`-algebra `C` embeds unitally in
`M_e(F_k)` for some `e` and `k`.

*Proof.*
- **Reduce to primary pieces.** Write `C = Q[y_1..y_r]/J` and take a primary
  decomposition `J = q_1 ∩ ... ∩ q_l` (Lasker--Noether). Then `C` embeds in
  `Π_j Q[y]/q_j`. So it suffices to embed each primary ring `A = Q[y]/q` unitally in some
  `M_(e_j)(F_(k_j))`, and then use block-diagonal matrices over `F_k`, `k = max k_j`,
  since `F_(k_j) ⊆ F_k`. If every `k_j = 0`, use `Q ⊆ F_1` and `k = 1`.
- **The primary case.** By Noether normalization there is an injective finite
  `Q`-algebra map `Q[t_1..t_k] = A_0 -> A`.
  - A nonzero `a ∈ A_0` is not nilpotent in `A`, since `A_0` is reduced and injects.
  - Every zero divisor of the primary ring `A` is nilpotent, so `a` is a non-zero-divisor.
  - Hence `A` is torsion-free over `A_0`, and `A -> A ⊗_(A_0) F_k` is injective.
- **Regular representation.** `A ⊗ F_k` is a finite-dimensional `F_k`-algebra, of
  dimension `e` say. Its left regular representation is a unital injective homomorphism
  into `End_(F_k)(A ⊗ F_k) ≅ M_e(F_k)`. ∎

## 3. Proof of the claim
- **The coefficient ring.** Let `C_0 ⊆ M_D(C ⊗ Q<x>)` be the given subring. By hypothesis,
  or by §2 and special case 2 below, `C ⊆ M_e(F_k)` unitally. So
  `C ⊗_Q Q<x> ⊆ M_e(F_k) ⊗_Q Q<x> = M_e(F_k<x_1..x_m>)`, by flatness over the field `Q`.
- **Into `R_k`.** `F_k<x_1..x_m>` embeds in `R_k` unitally on `F_k`, by
  `rational-function-fields-embed-in-fp-simple-rings`, part 3. Hence
  `C_0 ⊆ M_D(M_e(F_k<x>)) ⊆ M_(De)(R_k)`, which is finitely presented and simple by §1.
- **Special cases.**
  1. *Commutative inputs.* A commutative ring `A` that is torsion-free and finitely
     generated as a ring lies in `A ⊗ Q`, a finitely generated commutative `Q`-algebra.
  2. *Finitely generated fields.* A finitely generated field `E` of characteristic zero is
     a finite extension of some `F_k`, a purely transcendental extension of `Q`. Its
     regular representation gives `E ⊆ M_e(F_k)`, hence `M_n(E) ⊆ M_(ne)(F_k)`.
  3. *Matrices over a field.* The entries of finitely many generators of a subring of
     `M_n(F)` generate a finitely generated subring, and its fraction field is a
     finitely generated field `E ⊆ F`. Then apply case 2.
  4. *Free algebras.* These are the case `C = E`, which is allowed by case 2.
- **Group consequence.** `GL_n(E) ⊆ GL_(ne)(F_k) ⊆ M_(ne)(R_k)^x`. ∎
