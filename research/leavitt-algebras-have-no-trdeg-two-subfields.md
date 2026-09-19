---
rg: 2
id: leavitt-algebras-have-no-trdeg-two-subfields
kind: claim
title: For every field k, matrix rings over L_k(1,2) contain no commutative subfield of transcendence degree two, so no commuting independent pair has all nonzero polynomials in it invertible
distinct_from:
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that forbids a polynomial subring k[a, b] (Ara--Cortiñas Q5.7), which is open; this forbids only the field-type pairs, where every nonzero p(a, b) is invertible, and it is proved.
  leavitt-algebra-hochschild-dimension-at-most-one: that is the bimodule bound pd_(L^e) L <= 1; this is its consequence for subfields.
  leavitt-homogeneous-commuting-pairs-are-algebraically-dependent: that treats homogeneous pairs for the grading; this treats field-type pairs of arbitrary degree.
---

**ESTABLISHED** by `leavitt-subfield-bound-from-hochschild-dimension` (unreviewed).

Let `k` be a field, `L = L_k(1,2)` and `r >= 1`.
- Every commutative subfield `F ⊆ M_r(L)` with `k · 1 ⊆ F` has `trdeg_k F <= 1`.
- Equivalently, if `a, b ∈ M_r(L)` commute and every `p(a, b)` with `p ∈ k[x, y] ∖ 0` is invertible, then `a` and
  `b` are algebraically dependent.

**What is left of Ara--Cortiñas Q5.7.** A polynomial subring `k[a, b] ⊆ L` must now have some nonzero `p(a, b)`
that is not invertible in `L`. For example, a one-sided unit `u` with `vu = 1` and `uv ≠ 1` is a zero divisor,
since `(1 - uv) u = 0`.

The homological method stops exactly there. The lower bound in `quasi-free-subfield-bound-via-koszul-ext` §2
needs `L` to be flat, or free, over the commutative subring. That fails for `k[a, b]` as soon as some `p(a, b)` is
a zero divisor in `L`.
