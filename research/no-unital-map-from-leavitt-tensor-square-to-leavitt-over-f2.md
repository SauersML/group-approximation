---
rg: 2
id: no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2
kind: claim
title: There is no unital homomorphism from L_(F_2)(1,2) ⊗ L_(F_2)(1,2) to L_(F_2)(1,2)
distinct_from:
  leavitt-tensor-powers-are-left-coherent: that is coherence of tensor powers, whose Attempts record the embedding question as open; this is the embedding question itself in characteristic two, as a target for implications.
  leavitt-commuting-units-are-algebraically-dependent: that is a statement about pairs of commuting units; this is the tensor-square nonembedding that it implies.
---

**OPEN.** Let `L = L_(F_2)(1,2)`. No unital ring homomorphism `L ⊗_(F_2) L -> L` exists. Since `L ⊗ L` is
simple, the same statement holds for unital embeddings.

**Source of the question.** P. Ara and G. Cortiñas, *Tensor products of Leavitt path algebras*,
arXiv:1108.0352v3, page 8, checked against the PDF on 2026-09-13. The paper works over a field `k`.
- The question reads verbatim: "Question 5.7. Is there a unital homomorphism φ: L_2 ⊗ L_2 → L_2?"
- The paper then observes: "to build a unital homomorphism φ: L_2 ⊗ L_2 → L_2, it is enough to exhibit a
  non-zero homomorphism ψ: L_2 ⊗ L_2 → L_2, because eL_2e ≅ L_2 for every non-zero idempotent e in L_2."

So this claim is the case `k = F_2`, and it is equivalent to the absence of any nonzero homomorphism
`L ⊗ L -> L`.

**What it would change.**
- A positive answer, a unital embedding, would put the Brin--Thompson-type unit group `(L ⊗ L)^x`, which contains
  `V × V`, inside `L^x`.
- It would also refute `leavitt-commuting-units-are-algebraically-dependent` and
  `leavitt-unit-centralizers-have-finite-rank`.
- A negative answer follows from `leavitt-commuting-units-are-algebraically-dependent`
  (`tensor-square-nonembedding-from-algebraic-dependence`).

## Attempts

**K-theory.** It gives no obstruction: `K_*(L) = K_*(L ⊗ L) = 0` (`ara-cortinas-leavitt-tensor-k-theory-vanishes`).

**Commuting units.** A unital map sends `c ⊗ 1` and `1 ⊗ c`, for the north--south unit `c`, to algebraically
independent commuting units. An obstruction to such pairs in `L` therefore decides the question; see the route
above. No such obstruction is proved.
