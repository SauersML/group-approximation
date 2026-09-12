---
rg: 2
id: leavitt-tensor-powers-are-left-coherent
kind: claim
title: Every tensor power of L_k(1,2) with at least two factors is left coherent
refuted_by: [leavitt-tensor-powers-are-not-left-coherent]
distinct_from:
  leavitt-tensor-powers-have-trivial-k-theory: that is vanishing of K_1 and K_2 for three or more factors; this is coherence for two or more factors, a ring-theoretic input that implies it through the global dimension bound and the regular coherent import.
---

**REFUTED** by `leavitt-tensor-powers-are-not-left-coherent` (attempt 9).
The claim was: for every field `k` and every `d >= 2`, `L_k(1,2)^(⊗d)` is left
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
6. **Free-variable induction (withdrawn before landing).** The plan was to
   induct on `L^(⊗m) ⊗ k<Y> ⊗ k[t_1..t_n]`, producing each new Leavitt factor
   by localizing two fresh free variables over the field.
   *Dies* at its first step: `k<Y> ⊗ k<x_1, x_2>` is not `k<Y ⊔ {x_1, x_2}>`,
   because variables in different tensor factors commute. The ring being
   localized is again a free algebra over a non-noetherian coefficient ring,
   which is the gap of attempt 1.
7. **The conditional warning cited in attempt 1 never fires.** Attempt 6 of
   `leavitt-tensor-powers-have-trivial-k-theory` assumes that `k<e,f> -> k[F_2]`
   is flat. It is not flat on either side.
   - **Equational criterion.** A right `A`-module `U` is flat iff every relation
     `Σ u_i a_i = 0` factors as `u_i = Σ_j v_j b_(ji)` with `Σ_i b_(ji) a_i = 0`
     in `A` for each `j`.
   - **The failing relation.** In `k[F_2]`, `(−f e^(−1))·e + 1·f = 0`. In
     `k<e,f>`, `b_1 e + b_2 f = 0` forces `b_1 = b_2 = 0`: the monomials of
     `b_1 e` end in `e` and those of `b_2 f` end in `f`, and `k<e,f>` is a
     domain. So every factorization gives `u_2 = 0`, not `1`.
   - **Left side.** Apply the anti-automorphisms fixing `e` and `f`: word
     reversal on `k[F_2]` and on `k<e,f>`.

   So no counterexample is known to "free algebras over regular coherent rings
   are regular coherent", and attempt 1's input is open, not refuted. That input
   is coherence of `S<x_1, x_2>` for `S = L^(⊗(d-1))`.

   Bihler (arXiv:math/0612569v1, read on MSI) gives only permanence of
   Vogel-regularity for tensor algebras (Proposition 5). He remarks that
   Waldhausen's class Cl needs coherence conditions on the base ring. Waldhausen
   was not read here.
8. **Corner skew Laurent induction on the last factor.**
   `L^(⊗d) = R_0[t_+, t_-; α]` with `R_0 = L^(⊗(d-1)) ⊗ L_0`, `t_± = 1 ⊗ x_1,
   1 ⊗ y_1`, and `α = 1 ⊗ (x_1 · y_1)`. Here `R_0` is a flat filtering colimit of
   matrix rings over `L^(⊗(d-1))`. By Gersten's Proposition 1.6 (as quoted in
   ABC Section 7), `R_0` is regular supercoherent whenever `L^(⊗(d-1))` is.
   *Dies*: the generic step is false, even for automorphisms.
   - **The ring.** Let `B = k[x_i^(±1) : i ∈ Z]` with `σ` the shift.
     `B[t_1..t_n]` is a filtering union of noetherian regular rings along free
     extensions, so `B` is regular supercoherent by the same Proposition 1.6.
   - **Its Laurent extension.** `B[s^(±1); σ] = k[Z ≀ Z]`. Its augmentation ideal
     is finitely generated, and it is finitely presented only if `Z ≀ Z` is of
     type `FP_2` over `k`.
   - **Homology.** In the Lyndon--Hochschild--Serre spectral sequence of
     `Z^(⊕Z) ⋊ Z`, `E^2_(p,q) = 0` for `p >= 2`. So `H_2(Z ≀ Z; k)` contains
     `E^2_(0,2) = H_0(Z; Λ^2 k[t^(±1)])`, which has one basis vector
     `e_0 ∧ e_n` for each `n >= 1`. It is infinite-dimensional, so `Z ≀ Z` is not
     `FP_2` over `k`, and `k[Z ≀ Z]` is not coherent.

   A proof must therefore use the particular corner isomorphism, or the
   ultramatricial base `L_0^(⊗d)` of attempt 2. Regular supercoherence of the
   degree-zero ring is not enough.
9. **Refuted (lane `bh-coherence-corners`, 2026-09-12).** See
   `leavitt-tensor-powers-are-not-left-coherent`, with route
   `leavitt-tensor-powers-not-left-coherent-proof`.
   - **The ring.** The total-degree-zero ring `⊕_n L_n ⊗ L_(−n)` is the
     Bernoulli crossed product `(⊗'_(Z) M_2(k)) ⋊ Z`, with
     `u = x_1⊗y_1 + x_2⊗y_2` as the shift.
   - **The witness.** The left annihilator of `(1 − u) e`, with
     `e = x_1 y_1 ⊗ 1`, is not finitely generated. Its elements are constant
     along runs of ones in two-sided binary sequences, and runs of every length
     occur.
   - **Attempt 2 answered negatively.** Graded von Neumann regularity does not
     give coherence, even for a strong `Z`-grading.
   - **Attempt 1's input is false.** `L<x_1, x_2>` is not left coherent: its
     flat universal localization `L ⊗ L` would inherit coherence.
