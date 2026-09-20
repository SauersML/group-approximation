---
rg: 2
id: hochschild-dimension-bounds-commuting-independent-families
kind: claim
title: If pd_(A^e) A <= d, then no matrix ring over A contains d+1 commuting algebraically independent elements; so quasi-free algebras contain no k[x, y]
distinct_from:
  quasi-free-algebras-have-no-trdeg-two-subfields: that excludes commutative subfields of transcendence degree two, which needs every nonzero polynomial in the pair to be invertible. This excludes all commuting independent pairs, with no invertibility.
  leavitt-tensor-global-dimension-bound: that is the upper bound gl.dim(B ⊗ L^(⊗d)) <= gl.dim B + d. This pairs the same kind of upper bound with the polynomial-subring lower bound.
  polynomial-subrings-bound-transcendental-flat-dimension: that is the lower bound alone, for an arbitrary algebra. This is its combination with the bimodule upper bound.
---

**ESTABLISHED** by `commuting-rank-from-bimodule-resolution-and-koszul` (unreviewed).

Let `k` be a field, `A` a `k`-algebra with `pd_(A^e) A <= d`, where `A^e = A ⊗_k A^op`, and `r >= 1`. Then
`M_r(A)` has no commuting independent family (in the sense of
`polynomial-subrings-bound-transcendental-flat-dimension`) of size `d + 1`.

Equivalently, `k[x_1, ..., x_(d+1)]` has no injective algebra map, unital or not, into `M_r(A)`. The same holds
for `k[Z^(d+1)]` and for every ring containing it.

**Case `d = 1` (quasi-free algebras in the sense of Cuntz--Quillen).** Matrix rings over a quasi-free algebra
contain no copy of `k[x, y]`. Any two commuting elements `a, b` satisfy `P(a, b) = 0` for some nonzero `P`.
This covers free algebras, where it recovers a consequence of Bergman's centralizer theorem, and path
algebras of finite quivers. It also covers `L_k(1,2)`, by `leavitt-algebra-hochschild-dimension-at-most-one`.
Hochschild dimension one for other universal localizations is not asserted here.
