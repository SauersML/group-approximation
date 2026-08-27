---
rg: 2
id: native-b1-completeness-projective-split-proof
kind: route
title: Factor B1 through the p child and isolate the crossed q child
target: native-b1-completeness-factorization-stays-projective-times-c2
requires:
  - single-root-completeness-attachments-are-exhausted
  - finite-prefix-labelled-windows-remain-projective
  - projective-star-profile-has-zero-hecke-source
---

The binary coefficient products are

```text
p+q=1,
p b_1=s_0t_0s_0t_1=s_0t_1=b_1,
q b_1=s_1t_1s_0t_1=0,
(s_1t_0)b_1=s_1t_0s_0t_1=s_1t_1=q.                  (1)
```

Root additivity on `(7,10)` and the ordinary composable-root commutator law
on `(7,10),(10,2)` turn `(1)` into the first four rows of `(NBC2)`.
The last product in `(1)` gives the final anchored-cell row
`[A_1,B_1]=C_1`.  This proves the literal occurrence table.

For the finite factorization, use the ten distinct projective labels

```text
q@1,q@2,q@3,q@4,q@5,q@6,
e_1@7,e_2@8,e_3@9,e_1@10.                             (2)
```

The coefficient of every standard arrow from label `u` to label `v` is
`s_ut_v`.  In particular

```text
P=x_(7,10)(s_0t_0),       B'=x_(10,2)(s_0t_1),       (3)
```

and their product is the already named arrow `B_1`.  The projective
matrix-unit lift therefore puts `(3)`, the old `SL_9` head, and every other
standard arrow among `(2)` inside a literal `SL_10(F_2)`.

Now `Q=x_(7,10)(q)` acts between the complementary q projective corners at
the two coordinates labelled `0` in `(2)`.  Any projective-head root incident
to `7` or `10` has at that endpoint a coefficient with a factor `s_0` or
`t_0`.  The identities

```text
q s_0=0,                  t_0q=0                     (4)
```

make every composable elementary-matrix product with `Q` vanish.  Roots
sharing only one endpoint and distant roots commute as usual.  Hence `Q`
centralizes the projective `SL_10` in the elementary image.  It is a
nonidentity involution on the orthogonal q subcorners, so the two elementary
image factors intersect trivially.  This proves `(NBC3)`.  As before, the
finite representation is obtained after the canonical elementary
projection, so no opposite-root statement about the ambient Steinberg
kernel is needed.

In the natural nonzero-vector permutation representation of `SL_10(F_2)`,
a transvection has `2^8=256` two-cycles, while the all-negative three-root
star character has `2^(10-4)=64` copies.  The negative-stabilizer certificate
for the full-Hecke signed average is unchanged by the new spectator label,
so its image is zero.  Tensoring with the regular `C_2` doubles the two ranks
and leaves the source operator zero, proving `(NBC4)`.
