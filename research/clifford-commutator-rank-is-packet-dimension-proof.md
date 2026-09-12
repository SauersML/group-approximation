---
rg: 2
id: clifford-commutator-rank-is-packet-dimension-proof
kind: route
title: Independent row and column normalization, then count Pauli pairs
target: clifford-commutator-rank-is-packet-dimension
requires: []
---

Fix the assignment `x` and put `r = rank_F2 M(x)`.  Choose `R, C` in
`GL_m(F_2)` with

```text
R M(x) C = diag(I_r, 0).
```

Replace the generators by `p'_i = prod_j p_j^(R_ij)` and
`q'_j = prod_i q_i^(C_ij)`.  This is legitimate because the `p_j` commute among
themselves and the `q_i` commute among themselves, so the products are again
commuting involutions, and `R, C` invertible means the new generators generate
the same subgroups.  Bilinearity of the commutator pairing in a class-two group
means the commutation matrix of the primed generators is exactly `R M(x) C`.

Note the two normalizations are independent: the `p`-side and the `q`-side are
different generator sets, so the form is a bilinear map
`F_2^m x F_2^m -> F_2` rather than an alternating form on a single space, and
the normal form is `diag(I_r, 0)` with `r` the ordinary rank.

In the normalized generators, for `i, j <= r` we have `P'_i Q'_i = -Q'_i P'_i`
and `P'_i Q'_j = Q'_j P'_i` for `i != j`, so `(P'_1,Q'_1),...,(P'_r,Q'_r)` are
`r` mutually commuting anticommuting pairs.  They generate an extraspecial
2-group of order `2^(2r+1)` on which the central involution acts as `-1`, whose
unique such sector is `M_(2^r)(C)`.

The remaining generators `P'_i` for `i > r` have zero row and `Q'_j` for
`j > r` have zero column, so each commutes with everything in the sector; being
involutions they generate `C[(C_2)^(2(m-r))]`.  Since these commute with the
Pauli part and the two families together generate the sector, the sector algebra
is the tensor product `(CRP3)`.

A tensor product of `M_(2^r)(C)` with a commutative algebra of dimension
`2^(2(m-r))` is a direct sum of `2^(2(m-r))` copies of `M_(2^r)(C)`, so every
simple block has dimension `2^r`.
