---
rg: 2
id: scalar-bs14-exit-gram-and-phase-proof
kind: route
title: Compute the weighted return shift and separate active from passive exits
target: scalar-bs14-exit-angle-energy-dichotomy
requires:
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
  - bs14-unitary-representations-are-periodic-cycle-packets
---

Put `e=Xq` and `e_i=Y_i^2q`.  The internal three-cycle Gram relations give

```text
<q,e>=<q,e_i>=<e,e_i>=a.
```

The projection of each `e_i` onto `span(q,e)` is
`a(q+e)/(1+a)`.  Subtracting these projections gives `(SAE3)`, because

```text
<e_1,e_2>=<Xq,U_1^*U_2Xq>
          =a^2+(1-a^2)<z,gz>.
```

Dividing the cross entry by the common squared norm yields `(SAE2)`.

For the packet computation, use a basis `e_j`, `j in Z/m`, with

```text
S e_j=lambda^(4^j)e_j,
R e_j=e_(j-1)
```

and insert the scalar return `v` on the closing edge.  Then

```text
S^(-2) R S e_j=lambda^(2*4^(j-1))e_(j-1),             (SEG1)
```

again with the return scalar on the closing edge.  Multiplying the `m`
weights proves `(SAE4)`.  The numerical range of a normal cyclic shift is
the convex hull of its spectrum, so equal weight on the conjugate roots
`exp(+-2 pi i/m)` gives `(SAE5)`.

Finally,

```text
f(a)/(1-a^2)^2=4(1+2a)/(1+a)^5 >=3/8                (SEG2)
```

for `0<=a<=1`; the last function decreases to `3/8` at `a=1`.
Summing `(SEG2)` over the active eigenvalues proves `(SAE7)`.  On the
passive subspace, the squared Frobenius norm of the off-diagonal corner
`PXQ` is `sum_j(1-a_j^2)<=tau k`, giving the stated normalized-HS cost.
