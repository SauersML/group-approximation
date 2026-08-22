---
rg: 2
id: atlas-a4-two-c3-line-angle-proof
kind: route
title: Compress one C3 averaging projection to the left-coset basis of the other
target: atlas-a4-two-c3-line-carriers-have-exact-angle-gap
requires:
  - atlas-a4-rank-three-core
artifacts:
  - experiments/atlas_a4_c3_line_connection_spectrum.py
---

The exact `F2` matrices from the rank-three core generate two order-six
groups and then `H` of order `168`.  The normal order-three subgroups generate
all of `H`, proving that the intersection of the two fixed spaces is the
constant line.

Use the `56` normalized left-`C_K`-coset indicators as a basis of
`ran(P_K)`.  In this basis

```text
P_K P_6 P_K=B/9
```

for an integer symmetric matrix `B`: its `(D,C)` entry counts the pairs
`(h,x)` with `h in C_6`, `x in C`, and `hx in D`.  The artifact constructs
this matrix by exact finite-field multiplication.  Integer matrix arithmetic
verifies its minimal polynomial divides

```text
x(x-9)(x-2)(x-4)(x^2-6x+1)(x^2-9x+16),                (A4-C3-5)
```

and its power traces through degree eight give multiplicities

```text
7,1,12,6,8,8,7,7
```

for the roots in the order displayed in `(A4-C3-2)`.  This proves the exact
spectrum.  Removing the eigenvalue-one constant line leaves the maximum
`lambda_*`; the projection identity
`||(1-P_6)z||^2=||z||^2-||P_6z||^2` proves `(A4-C3-4)`.

