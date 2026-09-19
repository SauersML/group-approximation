---
rg: 2
id: nested-prefix-clique-forces-centralizer-area-divergence
kind: claim
title: Nested-prefix clique conjugacy cells force forbidden centralizer fillings
distinct_from:
  leavitt-chromatic-tables-have-area-divergence: that freezes a column already commuting with infinitely many rows; this extracts a uniformly filled fixed-centralizer section from the three conjugacy-difference edges of each exponent-two triangle.
  finite-mark-centralizer-commutator-area-is-proper: that is the abstract properness theorem; this supplies the concrete infinite family of distinct centralizer cosets from the nested Leavitt root clique.
---

**ESTABLISHED.**  In every finite presentation of

```text
Delta=St_20(L_(F_2)(1,2)),            z=x_13(s_1t_1),
```

the conjugacy-difference filling areas of
`leavitt-nested-prefix-conjugacy-clique` are unbounded, for every choice of
vertex representatives and edge conjugators.

Indeed fix a representative of `b_0` and put

```text
c_m=b_0^(-1)b_m,                       m>=1.            (NCD1)
```

All `c_m` lie in the same characteristic-two root subgroup.  Hence they are
commuting involutions.  The elements `c_m`, `m>=2`, occupy infinitely many
distinct cosets modulo `<c_1>`.

Suppose every edge difference had conjugacy area at most `A`.  The edges
`(0,1)`, `(0,m)`, and `(1,m)` say, with this same bound, that

```text
c_1,                 c_m,                 c_1^(-1)c_m
```

are conjugate to the fixed involution `z`.  Filling their squares and then
the elementary exponent-two triangle proves

```text
Area([c_1,c_m])<=C_A                                  (NCD2)
```

with one constant independent of `m`.  This contradicts
`finite-mark-centralizer-commutator-area-is-proper`, applied to the fixed
nontrivial involution `c_1` and the distinct cosets represented by the
`c_m`.  Therefore the nested-prefix exact clique cannot have a uniform
conjugacy-difference area bound.

DERIVATION
nested-prefix-centralizer-area-divergence-proof
