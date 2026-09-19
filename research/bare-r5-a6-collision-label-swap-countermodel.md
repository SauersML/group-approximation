---
rg: 2
id: bare-r5-a6-collision-label-swap-countermodel
kind: route
title: Swap the common Carmichael labels inside the standard A6 module
target: bare-r5-a6-collision-does-not-synchronize-shared-labels
requires: []
---

Bleak--Quick's fifth relation is

```text
R5=[(000 010),(10 110)]=1,
```

or, in their three generators `a=(00 01)`, `b=(01 10 11)`, and
`c=(1 00)`,

```text
[a^(bcabca),a^(bcacabab^(-1)a)]=1.                 (BRP1)
```

It is a disjoint-support commutator.  For the Carmichael generators
`c_i=(i p q)`, direct multiplication gives

```text
c_i c_j=(i p)(j q)                                 (i!=j). (BRP2)
```

The two transpositions in `(BRP2)` are disjoint.  After sending the four
prefixes in R5 to `i,p,j,q`, a conjugate of `(BRP1)` is precisely
`(c_i c_j)^2=1`.  In particular, the R5 cell across two adjacent charts'
nonshared leaves mentions neither shared label.

Now use the standard action of `A6` on

```text
H={(z_1,...,z_6) in C^6 : sum z_i=0}.
```

Restriction of the permutation matrices to `H` gives a unitary
five-dimensional representation.  The four operators `c_i|_H` satisfy all
the Carmichael relations, hence the two contextual triples in `(BRS1)` have
zero local defect and their nonshared R5 relation has zero defect.

It remains only to calculate the mismatch.  For `i!=j`, the permutation
`c_i^(-1)c_j` is a three-cycle and therefore has three fixed points in the
six-point permutation action.  Its character on `H` is `3-1=2`.  Hence

```text
||c_i-c_j||_(2,H)^2
 =2-2 Re(tr_H(c_i^(-1)c_j))
 =2-2(2/5)=6/5.                                    (BRP3)
```

Taking `(i,j)=(1,2)` proves both equalities in `(BRS3)`.  The known
irreducible degrees `1,5,5,8,8,9,10` of `A6` also show that dimension five
is the smallest dimension in which this nontrivial exact A6 label-swap
countermodel can occur.

