---
rg: 2
id: whitehead-swap-copy-completion-proof
kind: route
title: Multiply the complementary Whitehead corners and realize them on a finite two-chart carrier
target: whitehead-swap-copy-completion-retains-rectangular-escape
requires: []
---

From `t_i s_j=delta_(i,j)` and `p+q=1`, direct multiplication gives

```text
j^2=p+q=1,
j(q+s_0gt_0)j=p+s_1gt_1.                               (WSP1)
```

The two summands in `(WSC2)` are block diagonal for the orthogonal corners
`p,q`; their product is `(WSC3)`.  Applying
`Phi_1(r)_(a,b)=t_a r s_b` gives `(WSC4)` entry by entry.

For the finite model, `V=U^*`.  The four block products are

```text
UV=diag(s_0t_0+s_1t_1,t_1s_1)=1_(F direct sum E),
VU=diag(t_0s_0,s_0t_0+s_1t_1)=1_(E direct sum F),        (WSP2)
```

and the off-diagonal blocks vanish by `t_i s_j=0` for `i!=j`.  The same
four-block multiplication with `diag(g,1_F)` inserted proves `(WSC6)`.

Finally, `s_4` vanishes on the identity extension because its alternating
coefficients sum to zero.  It has norm `8` on the two-qubit `F` block by
`four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap`.  Normalized
Hilbert--Schmidt norm squares weight orthogonal blocks by their dimension,
so extending from `F` to `F direct sum E` multiplies the norm by
`sqrt(dim(F)/(dim(F)+dim(E)))=sqrt(2/3)`, proving `(WSC9)`.

