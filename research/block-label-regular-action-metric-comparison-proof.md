---
rg: 2
id: block-label-regular-action-metric-comparison-proof
kind: route
title: Compare a finite block-label wreath representation with its regular fiber action
target: uniformly-discrete-block-monomial-images-are-sofic
requires: []
---

By bi-invariance it is enough to compare one block-monomial element
`A=(ell_i,sigma)` with the identity.  Split the base coordinates into

```text
M={i:sigma(i)!=i},
S={i:sigma(i)=i and ell_i!=1}.                          (BLR1)
```

The permutation action `(UDB3)` moves every point above `M union S` and
fixes every point above its complement, because left translation by a
nonidentity element of `L_n` has no fixed points.  Therefore

```text
h_n(A,1)=(|M|+|S|)/|I_n|.                              (BLR2)
```

The normalized trace of the block-monomial matrix receives no diagonal
contribution from `M`, receives `tr_(r_n)(pi_n(ell_i))` from `S`, and
receives one from every remaining block.  Hence

```text
(1/2)||A-1||_2^2
 = |M|/|I_n|
   +(1/|I_n|) sum_(i in S)
      (1-Re tr_(r_n)(pi_n(ell_i))).                     (BLR3)
```

Every summand in `(BLR3)` lies in `[delta,2]`, proving `(UDB4)`.  Apply
`(UDB4)` to the multiplication defects and to distances from the identity.
The regular fiber actions then define a homomorphism of `G/N` into a metric
ultraproduct of finite symmetric groups, with trivial kernel.  Thus `G/N`
is sofic.
