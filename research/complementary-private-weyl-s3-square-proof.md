---
rg: 2
id: complementary-private-weyl-s3-square-proof
kind: route
title: Split the native Weyl S3 diagonally across the two complementary branches
target: complementary-private-weyl-loops-have-s3-square-gauge-model
requires:
  - complementary-depth-two-a3-whiteheads-have-a6-gauge-model
  - native-weyl-return-gauges-have-s3-model
---

Root additivity and completeness give the first two factorizations in
`(CPW2)`.  Orthogonality of `q_0,q_1` makes every root operator from
different branches commute.  Hence

```text
nV_in
 =(P_iP_(1-i))V_i(P_iP_(1-i))
 =P_iV_iP_i=R_i,                                      (CPWP1)
```

where the last equality is the branch partial-Whitehead conjugacy.  The
same calculation with `R_i` proves `mV_im=P_i`.  Since the full Weyl swaps
`P_i` and `R_i`, it fixes their symmetric Whitehead word `V_i`, proving the
third row of `(CPW3)`.

For the finite model, each factor of `S_3 times S_3` contains the standard
three reflections `a,b,c=aba`.  The branchwise equations reduce to

```text
a c a=b,             b c b=a,             c c c=c.   (CPWP2)
```

The two direct-product factors commute, so multiplying branch-zero and
branch-one elements proves all aggregate factorizations and commutators.
Finally `ca` is a three-cycle, proving `(CPW8)`.
