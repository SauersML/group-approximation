---
rg: 2
id: regular-coherent-coefficients-leavitt-k-theory-citation
kind: route
title: Specialize the Leavitt path sequence to one vertex with two loops under regular coherent coefficients
target: regular-coherent-coefficients-kill-leavitt-tensor-k-theory
requires: []
---

**Source.** P. Ara, M. Brustenga, G. Cortiñas, *K-theory of Leavitt path
algebras*, arXiv:0903.0056v2. All statements below were read from the PDF text on
MSI on 2026-09-12; quotations are verbatim, up to extraction of symbols. ABC's
bibliography:
- [5]: F. Bihler, *Vogel's notion of regularity for non-coherent rings*,
  arXiv:math/0612569v1;
- [17]: S. M. Gersten, *K-theory of free rings*, Comm. Algebra 1 (1974) 39–64;
- [30]: F. Waldhausen, *Algebraic K-theory of generalized free products I*,
  Ann. of Math. (2) 108 (1978) 135–204.

## Verbatim inputs

- **Theorem 5.10.** "Let A be an H′-unital ring, E a finite quiver ... Assume the
  quiver E has no sources. We have K(L_A(E)) ≃ NK(L_0 ⊗ A; φ⊗1)_+ ⊕
  NK(L_0 ⊗ A; φ⊗1)_− ⊕ hocofiber(K(A)^(e_0 − e'_0) --(1 − N^t)--> K(A)^(e_0))."
  This is an equivalence of spectra, so it holds degree by degree.
- **Notation 3.4.1.** "Define NK(A;φ)_+ = hocofiber(K(A) → K(A[t;φ])) ... We have
  K(A[t;φ]) = K(A) ⊕ NK(A;φ)_+". For an endomorphism, `NK(A;φ)_±` is defined
  through the colimit `B = φ^(-1) A`, "and we can extend it to the unitization
  B~". So the twisted Nil groups are degree-preserving summands.
- **Proof of Proposition 7.1.** It concerns `D = B ⊕ k`, the `k`-unitization of
  `B = φ^(-1) L_0`, and states: "it suffices to show that D is regular coherent
  whenever k is so." The argument is [17, Proposition 1.6] on flat filtering
  colimits of regular coherent rings, applied to matrix algebras over `k`.
- **Proof of Lemma 7.2** (for an automorphism `φ` of `R`): "For n ≥ 1 this
  follows from [30, Theorem 4], because, as we observed before,
  R[t_1, t_1^−1, ..., t_p, t_p^−1] is regular coherent. Let n ≤ 1 and assume
  ... Since R[t, t^−1] is regular supercoherent ..."
- **Remark 7.8.** "If we only assume that k is regular coherent in Theorem 7.6,
  then the long exact sequence in the statement terminates at K_0(L_k(E)),
  although conjecturally the long exact sequence should still stand under this
  weaker hypothesis on k, see [5]."

## Derivation, degree by degree

Let `E` be the quiver with one vertex and two loops, so
`L_R(E) = R ⊗ L_Z(1,2)`. `E` has no sources and no sinks: `e_0 = 1`,
`e'_0 = 0`, `N_E = (2)`. Let `R` be regular coherent and `n >= 1`.

1. **Cofibre term.** `1 − N^t = −1` is an equivalence, so the hocofiber is
   contractible. By Theorem 5.10,
   `K_n(L_R(E)) = NK_n(L_0 ⊗ R; φ)_+ ⊕ NK_n(L_0 ⊗ R; φ)_−`.
2. **Pass to the unitized colimit.** By Notation 3.4.1,
   `NK(L_0 ⊗ R; φ)_± = NK(B~; φ^)_±`, with `B = φ^(-1)(L_0 ⊗ R)` H′-unital.
   Excision for the ideal `B` identifies this with the part of
   `NK(D; φ^)_±`, `D = B ⊕ R`, not coming from `R`. So it is a direct summand
   of `NK_n(D; φ^)_±`.
3. **`D` is regular coherent.** This is the reduction inside the proof of
   Proposition 7.1, which uses regular coherence of the coefficient ring only.
4. **Twisted Nil vanishes.** `φ^` is an automorphism of `D`. The `n >= 1` case
   of Lemma 7.2 with `p = 0` needs only that `D` is regular coherent, and gives
   `NK_n(D; φ^)_± = 0`.
5. **Conclusion.** By steps 1, 2 and 4, `K_n(R ⊗ L_Z(1,2)) = 0` for every
   `n >= 1`.

**Where supercoherence is used.** Only in the downward induction of Lemma 7.2,
for degrees `n <= 0`, and in the unitization identity of Proposition 7.5 in those
degrees. That is the negative-degree continuation which Remark 7.8 calls
conjectural. The statement imported here is unaffected by it.
