---
rg: 2
id: exact-core-normal-quotient-descent-counterexample-proof
kind: route
title: Use the two-by-two cyclic Stinespring obstruction to disprove automatic quotient descent
target: exact-core-domain-does-not-descend-to-normal-quotient
requires: []
---

Let `Gamma=F(a,x)`. On `C^2` take

```text
pi(a)=diag(1,-1),       pi(x)=[[0,1],[1,0]],       V(1)=e_1.
```

The ucp map `Theta(y)=V^*pi(y)V` is the trivial character on
`C^*(<a>)`; hence that core lies in its multiplicative domain and
`pi(a)V=V`. But `pi(xax^(-1))V=-V`. Since `e_1` and
`pi(x)e_1=e_2` span `C^2`, this Stinespring representation is minimal
and does not annihilate the normal closure of `a`. Thus exactness on the
core controls only the vacuum row, not its word translates, and does not
force descent to `Gamma/<<a>>`.
