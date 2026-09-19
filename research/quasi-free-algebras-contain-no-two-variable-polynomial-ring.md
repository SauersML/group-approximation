---
rg: 2
id: quasi-free-algebras-contain-no-two-variable-polynomial-ring
kind: claim
title: A k-algebra of Hochschild dimension at most one, and every matrix ring over it, contains no polynomial ring in two variables
distinct_from:
  quasi-free-algebras-have-no-trdeg-two-subfields: that bounds commutative SUBFIELDS, whose lower bound needs the ambient ring to be free over the subfield; this bounds arbitrary commutative polynomial SUBRINGS, with no flatness of A over the subring, by resolving the fraction field of the subring instead of the subring itself.
  leavitt-algebras-have-no-trdeg-two-subfields: that is the subfield statement for the Leavitt algebra; this is the general polynomial-subring statement, which implies the plane-freeness of the Leavitt algebra.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that is the Leavitt instance; this is the general homological statement it follows from.
---

**ESTABLISHED** by `polynomial-subring-bound-via-fraction-field-koszul-ext` (unreviewed).

Let `k` be a field and `A'` a `k`-algebra. Suppose `C = k[a_1, ..., a_n] ⊆ A'` is a commutative subalgebra with
`1_(A') ∈ C` and `a_1, ..., a_n` algebraically independent over `k`. Put `K = k(y_1, ..., y_n)`.

1. **Lower bound.** `l.gl.dim(A' ⊗_k K) >= n`. No flatness of `A'` over `C` is assumed.
2. **Consequence.** Let `A` be a `k`-algebra with `pd_(A^e) A <= 1`. For every `r >= 1`, no two commuting elements
   of `M_r(A)` are algebraically independent over `k`. Equivalently, `k[x, y]` has no embedding into `M_r(A)`,
   unital or not.

The upper bound used in 2 is part 1 of `quasi-free-algebras-have-no-trdeg-two-subfields`:
`l.gl.dim(A ⊗_k U) <= 1` for every semisimple `U`.

**Why it matters.** The subfield version needed every nonzero `p(a, b)` to be invertible. Commuting pairs in the
Leavitt algebra, such as `k[s_0]`, are far from that, and the live need `03f81334` asked for exactly this
flatness-free bound. With `leavitt-algebra-hochschild-dimension-at-most-one` it settles
`leavitt-algebras-contain-no-two-variable-polynomial-ring` for every field, and with it Ara--Cortiñas Question 5.7.

## Attempts
