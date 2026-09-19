---
rg: 2
id: leavitt-polynomial-pairs-move-to-the-nonnegative-part
kind: claim
title: If L_k(1,2) contains a polynomial ring in two variables, then so does its nonnegative graded part
distinct_from:
  leavitt-nonnegative-part-is-matrix-union-over-free-algebra: that describes the nonnegative part and handles pairs already inside it; this asks to move a mixed-degree pair into it.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that is the full rank statement; this is only the transfer between L and its nonnegative part, true for example if both sides have rank 1.
  laurent-tensors-reduce-leavitt-rank-to-function-fields: that transfers rank between coefficient fields; this transfers it between degree ranges of the Z-grading.
---

**OPEN.** Let `k` be a field and `L = L_k(1,2)`, Z-graded by `deg s_i = 1`. Suppose `L` contains commuting
`k`-algebraically independent `a, b`. Then `L_(>=0) = ⊕_(n >= 0) L_n` contains such a pair.

**Status of the pieces.**
- By the involution `s_i ↔ t_i`, it is enough to reach `L_(>=0)` or `L_(<=0)`.
- Pairs with `a, b ∈ L_(>=0)` or `a, b ∈ L_(<=0)` need nothing.
- `L_0` is ultramatricial, hence algebraic. So a pair inside `L_0` never occurs, and some member of any pair has a
  nonzero component of nonzero degree.

**Why it can fail on its own.** `L_(>=0)` is stably finite, while `L` is purely infinite
(`leavitt-nonnegative-part-is-matrix-union-over-free-algebra`, consequence (d)). So no homomorphism
`L → L_(>=0)` does the transfer. A commuting pair could in principle use the infinite part, with genuinely
two-sided degree support.

## Attempts

**w16: ideas that fail.**
- *Leading forms.* This would take top-degree components of elements of `k[a, b]`. It fails because `L` is not a
  graded domain: `(s_0 t_0)(s_1 t_1) = 0` in degree 0. So leading forms of a domain can multiply to zero.
- *Conjugation.* Conjugation by homogeneous units, and the corner maps `x ↦ s_w x t_w`, preserve degree. So they
  cannot shift a negative-degree support into `L_(>=0)`.
- *Filtration.* `L = ∪_N t_0^N L_(>=0)` is a filtration by one-sided `L_(>=0)`-modules, not by subalgebras. It
  bounds the negative support of `k[a, b]` but does not move it.
