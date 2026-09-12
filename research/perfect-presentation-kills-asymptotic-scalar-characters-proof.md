---
rg: 2
id: perfect-presentation-kills-asymptotic-scalar-characters-proof
kind: route
title: Use the relator exponent lattice to kill every asymptotic scalar character
target: perfect-quotient-ir-survival-requires-nonscalar-mass
requires: []
---

Choose phases `lambda_(n,j)` with

```text
||S_n(x_j)-lambda_(n,j)1||_2->0.                        (PSP1)
```

The compressed polar maps are asymptotically multiplicative by `(IR1)`.
Therefore, for every fixed word `w`,

```text
S_n(w)-lambda_n^(exp(w))1 ->0 in normalized HS,        (PSP2)
```

where `exp(w) in Z^s` is its exponent-sum vector.  Condition `(IR2)` makes
`S_n(r_l)->1` for every defining relator, so `(PSP2)` gives

```text
lambda_n^(exp(r_l))->1                    (1<=l<=m).    (PSP3)
```

Perfectness says that the abelianized presentation is zero:

```text
Z^s / <exp(r_1),...,exp(r_m)> =0.                       (PSP4)
```

Hence for each standard basis vector `e_j` there are integers `c_(j,l)` with

```text
e_j=sum_l c_(j,l) exp(r_l).                             (PSP5)
```

Taking the corresponding products in `(PSP3)` proves
`lambda_(n,j)->1`.  Equation `(PSP1)` then gives `S_n(x_j)->1` for every
generator, and asymptotic multiplicativity gives `(PNS3)` for every fixed
word.

Finally, for a unitary `U`,

```text
inf_(|lambda|=1)||U-lambda 1||_2^2=2-2|tr(U)|.          (PSP6)
```

This proves the equivalence of `(PNS4)` and `(PNS5)` and completes the
claim.
