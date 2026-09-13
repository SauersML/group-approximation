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

**Source of the question.** This is the characteristic-two case of Ara--Cortiñas, arXiv:1108.0352v3,
Question 5.7, as recorded on `leavitt-tensor-powers-are-left-coherent` (Attempts, item 4). That record has not
been re-checked against the PDF here.

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
