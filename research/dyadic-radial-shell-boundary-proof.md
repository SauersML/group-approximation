---
rg: 2
id: dyadic-radial-shell-boundary-proof
kind: route
title: Compute the weighted Cheeger constant of the two Iwahori shell rays
target: dyadic-radial-shell-couplings-have-one-third-boundary
requires: []
---

The Iwahori `B` fixes the oriented edge `(v_0,v_1)`.  The elementary
root-group coordinates on either half-tree (equivalently, reduction of the
compact Iwahori modulo `2^(n+1)`) show that it is transitive on each set
`L_n,R_n`.  There are `2^n` choices after moving `n` steps away from the
edge, so

```text
|L_n|=|R_n|=2^n.                                      (DRS1)
```

The discrete arithmetic Iwahori has the same finite orbits: its reduction
onto every finite Iwahori quotient is surjective.  Orientation matters.
In the affine coordinate on `L_n`, the upper unipotent acts by translation
and hence has no fixed vertex for `n>=1`.  On the other half-tree it fixes
the vertex on its invariant end at every depth.  Hence `L_n` and `R_n` are
not isomorphic as `B`-sets for `n>=1`.  (`L_0` and `R_0` are both singleton
fixed orbits; allowing their harmless cross-match only improves the
finite-end constant and does not affect the estimate below.)

The radius-`p` sphere about `v_0` restricts to

```text
L_p disjointUnion R_(p-1),
```

where the second term is absent for `p=0`.  The radius-`q` sphere about
`v_1` restricts to

```text
R_q disjointUnion L_(q-1).                            (DRS2)
```

Consequently the two radial mixtures have oriented orbit multiplicities

```text
mult_0(L_n)=a_n,       mult_0(R_n)=a_(n+1),
mult_1(L_n)=b_(n+1),   mult_1(R_n)=b_n.               (DRS3)
```

The total mass of orbit sheets which cannot be matched is therefore

```text
M=sum_(n>=0) 2^n(
     |a_n-b_(n+1)|+|a_(n+1)-b_n|).                   (DRS4)
```

Split the variables into the two alternating rays

```text
a_0,b_1,a_2,b_3,...       and       b_0,a_1,b_2,a_3,... .
```

On either ray the edge joining positions `k,k+1` has weight `2^k`; the
vertex weights contributing to the sum of the two total dimensions are

```text
m_0=1,                 m_k=3*2^(k-1)  (k>=1).        (DRS5)
```

Every finite subset of a ray has weighted edge boundary at least one third
of its vertex mass.  It suffices to check an initial segment, since filling
gaps decreases boundary at fixed or larger mass; for `{0,...,N}` the two
quantities are

```text
2^N,                   1+sum_(k=1)^N 3*2^(k-1)
                       =3*2^N-2.                     (DRS6)
```

The layer-cake formula applies this weighted Cheeger inequality to arbitrary
nonnegative integer multiplicities.  Summing the two rays gives

```text
M >= (D_0+D_1)/3.                                    (DRS7)
```

When `D_0=D_1=D`, the maximum common union of equal oriented orbit sheets
has mass `D-M/2`, so at least `M/2>=D/3` points must be deleted from each
side.  Prefix plateaux make the ratio tend to `1/3`, so the constant for
this radial-sheet model is sharp.

