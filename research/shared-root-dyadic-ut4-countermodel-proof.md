---
rg: 2
id: shared-root-dyadic-ut4-countermodel-proof
kind: route
title: Use two nested Heisenberg subgroups of UT4 and odd periodic dyadic quotients
target: one-shared-root-plus-dyadic-depth-has-ut4-countermodels
requires: []
---

In any ring, elementary unitriangular multiplication gives

```text
[x_ij(s),x_jk(t)]=x_ik(st).
```

Apply this first to `(i,j,k)=(1,2,3)` and then to `(1,3,4)`.  The matrix
root `x_13` is literally the same subgroup in both equations.  Scaling a
root of height `j-i` by `2^(j-i)` respects products because heights add, so
`alpha` is an automorphism over `Z[1/2]` and preserves the two packets on
the same matrices.

The semidirect product in `(USD3)` acts on its depth quotient `L/N=Z`.
The base stabilizer contains all of `N`, while `h` moves the base point.
Adjoining commuting coordinate involutions therefore gives a base lamp
centralized by every root and a distinct commuting `h`-translate.

For the finite models, `q=2^L_0-1` is odd, so reduction of dyadic rationals
modulo `q` is defined.  Multiplication by `2` has exponent dividing `L_0`,
and hence the height-scaled automorphism has exponent dividing `L_0`.
This proves `(USD4)`.  A fixed nonzero dyadic matrix entry survives for all
sufficiently large `q`; a fixed nonzero depth survives modulo all
`L_0` larger than its absolute value; and a fixed finite lamp support stays
distinct modulo large `L_0`.  Choosing an increasing subsequence if needed
therefore separates every fixed nonidentity word.

In the regular character of `G_L`, the four lamp elements

```text
1, c_0, c_1, c_0c_1
```

are distinct.  Expanding `(1-c_0)(1-c_1)/4` gives `(USD5)`.  Every root,
shared-root, and dyadic relation has zero defect in the same representation.

