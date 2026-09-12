---
rg: 2
id: universal-central-selector-word-affinity-proof
kind: route
title: Compare the regular group-basis support of the marked scalarization
target: universal-central-selector-word-is-affine-for-any-actor
requires: []
---

Sum `(UCS3)` over all characters with `chi(J)=-1`.  Since their projections
sum to `p_-=(1-J)/2`, one obtains in `L(Gamma)`

```text
p_- w=sum_(chi(J)=-1) epsilon(chi)p_chi in C[D].                    (UCSP1)
```

The left regular representation is faithful on `C[Gamma]`, so `(UCSP1)` is
an equality of group-algebra elements.  Multiplying by two gives

```text
w-Jw in C[D].                                                       (UCSP2)
```

If `w` were outside `D`, then `w` and `Jw` would be two distinct group-basis
elements outside `D`.  Their coefficients `+1,-1` cannot cancel against an
element supported on `D`, contradicting `(UCSP2)`.  Hence `w in D`.

Every order-two word in the elementary abelian group `D` has the form
`J^c product_i z_i^(a_i)`.  Evaluating it at
`chi(z_i)=(-1)^(x_i)` gives

```text
epsilon(chi)=(-1)^(c+sum_i a_i x_i),
```

which is affine.

