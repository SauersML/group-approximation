---
rg: 2
id: q15-negative-via-toms
kind: route
title: The tracial completion of Toms's simple AH algebra without uniform Gamma is amenable, factorial, type II_1 and fails property Gamma
target: amenable-factorial-ii1-tracially-complete-without-gamma
requires:
  - toms-ah-counterexample-to-uniform-gamma
  - uniform-gamma-iff-completion-has-gamma
  - nuclear-tracial-completions-are-amenable
---

Unreviewed, as an assembly of established nodes. The credit for the counterexample is Toms's
(arXiv:2606.12188v2, Theorem 5).

1. **The algebra.** Let `A` be Toms's algebra. It is unital, simple, separable, nuclear,
   non-elementary and without uniform property Γ. Since `A` is unital, `T(A)` is compact. Let
   `(M, X)` be its tracial completion with respect to `X = T(A)`.
2. **Factorial.** CCEGSTW, arXiv:2310.20594v6, Proposition 3.23(iv), verbatim: "The completion
   (A^X, X̃) is factorial if and only if X is a face in T(A)". Here `X = T(A)` is a face of itself.
3. **Type II_1.**
   - `π_τ(M)'' = π_τ(A)''` by density.
   - A type `I_n` summand would give, through a character of its centre, a unital representation
     `A → M_n`.
   - A simple, non-elementary, infinite-dimensional unital algebra has no finite-dimensional
     representation.
4. **Amenable.** `A` is nuclear; apply the third prerequisite.
5. **No property Γ.** By the second prerequisite (CCEGSTW Proposition 5.20), `(M, X)` has property Γ
   iff `A` has uniform property Γ, and `A` does not.

**Designated traces.** `X` is the Poulsen simplex (`toms-doubling-ah-trace-simplex-is-poulsen`). For a
Bauer designated trace set, use route `q15-negative-via-bauer-pauli`.
