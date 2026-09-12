---
rg: 2
id: leavitt-tensor-powers-are-left-coherent
kind: claim
title: Every tensor power of L_k(1,2) with at least two factors is left coherent
distinct_from:
  leavitt-tensor-powers-have-trivial-k-theory: that is vanishing of K_1 and K_2 for three or more factors; this is coherence for two or more factors, a ring-theoretic input that implies it through the global dimension bound and the regular coherent import.
---

**OPEN.** For every field `k` and every `d >= 2`, `L_k(1,2)^(⊗d)` is left
coherent. It is then also right coherent, because the tensor product of the
involutions is an involution.

**Why it matters.** `leavitt-tensor-global-dimension-bound` then makes
`L^(⊗d)` regular coherent, and `regular-coherent-coefficients-kill-leavitt-tensor-k-theory`
gives `K_1 = K_2 = 0` for `L^(⊗(d+1))`. This is exactly the missing input of
`leavitt-tensor-powers-have-trivial-k-theory` and of its prime-field twin. For
`d = 1` it is known: `L(E)` is regular supercoherent (Ara--Cortiñas Lemma 6.1).

## Attempts

1. **Flat localization of a free algebra over the coefficients (Ara--Cortiñas
   Lemma 6.1 pattern).** `L ⊗ S = Σ^(-1)(S<x_1, x_2>)` is flat on the left by
   base change. Flat universal localizations preserve regular coherence (ABC
   Section 7).
   *Dies* at coherence of `S<x_1, x_2>` for `S = L^(⊗(d-1))`. Free algebras over
   regular coherent rings need not be coherent (conditional warning, Attempt 6
   of `leavitt-tensor-powers-have-trivial-k-theory`).
2. **Strong `Z^d`-grading over an ultramatricial base.** `A = L^(⊗d)` is
   strongly `Z^d`-graded, and `A_0 = L_0^(⊗d)` is a directed union of
   finite-dimensional semisimple algebras, hence von Neumann regular.
   - *Proved here:* every finitely generated graded left ideal is `A e` for an
     idempotent `e` in `A_0`. By Dade's theorem `I = A ⊗_(A_0) I_0`, and
     `I_0 = Σ A_(−g_i) x_i` is finitely generated because each `A_g` is finitely
     generated projective over `A_0`. So `A` is graded von Neumann regular,
     hence graded coherent.
   - *Stops* at passing from graded to ungraded coherence. That passage fails
     for non-abelian gradings: `k[F_2 × F_2]` is graded von Neumann regular for
     its group grading and is not coherent. For `Z^d` it is open. The noetherian
     analogue for polycyclic gradings does not transfer, because the
     leading-form ideal of a finitely generated ideal need not be finitely
     generated.
3. **Enveloping algebra.** The involution gives `L^op = L`, so `L ⊗ L = L^e`. By
   `leavitt-algebra-hochschild-dimension-at-most-one`, the diagonal module has
   the resolution `0 -> (L^e)^2 -> L^e -> L -> 0`.
   *Gives no obstruction*: the diagonal module is finitely presented.
4. **Absorbing a factor.** A unital embedding `L ⊗ L -> L` would reduce every
   power to `L`.
   *Unavailable*: Ara--Cortiñas arXiv:1108.0352v3 Question 5.7 asks whether a
   unital homomorphism `L_2 ⊗ L_2 -> L_2` exists, and it is open.
5. **Comparison with the group case.** `L ⊗ L` and `k[F_2 × F_2]` both have
   global dimension 2, and both are tensor squares of universal localizations of
   `k<x, y>`. The group ring is not coherent (Bieri--Stallings).
   *No transfer found*: `L ⊗ L` is simple, so there is no augmentation ideal from
   which to induce a finitely generated, not finitely presented left ideal.
   Neither coherence nor its failure is established.
