---
rg: 2
id: a5-carmichael-triangle-kernel-cover-proof
kind: route
title: Generate A5 by the three edge involutions and exclude a common minus line
target: a5-carmichael-triangle-covers-involution-kernels
requires: []
---

Each `s_ij` is an involution, so

```text
P_ij=(I+pi(s_ij))/2
```

is the orthogonal projection onto its `(+1)`-eigenspace.  The kernel of
`P=sum P_ij` is the intersection of the three `(-1)`-eigenspaces.

The first two involutions generate a dihedral group of order ten because

```text
s_12 s_23=(1,4,5,3,2).
```

The third involution is not in that dihedral group.  Indeed

```text
(s_12s_23)s_31=(1,3,5,4,2)
```

is a five-cycle, whereas a rotation times a reflection in `D_10` is again a
reflection; and `s_31` cannot itself be a rotation because it has order two.
The subgroup `D_10` is maximal in `A_5`, so the three involutions generate
`A_5`.

If `0!=xi in ker(P)`, every generator sends `xi` to `-xi`.  The line `C xi`
is therefore invariant under `A_5` and gives a one-dimensional character
which sends all three generators to `-1`.  This is impossible because `A_5`
is perfect.  Hence `P` has zero kernel in every representation.

There are finitely many irreducible representations of the finite group
`A_5`.  Taking the minimum of the least eigenvalues of `P` over them gives
`kappa_5>0`.  Finally

```text
||(I+pi(s_ij))xi||^2=4 <P_ij xi,xi>,
```

and summing proves `(A5K1)`.

For `(A5K2)`, the Fox rules give

```text
partial_g(b g^(-1)b g)
 = -b g^(-1)+b g^(-1)b
 = b g^(-1)(b-1).
```

Since `partial_g(s^2)=(1+s)partial_g(s)`, the displayed factorization
follows.
