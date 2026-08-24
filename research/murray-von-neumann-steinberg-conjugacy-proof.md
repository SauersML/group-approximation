---
rg: 2
id: murray-von-neumann-steinberg-conjugacy-proof
kind: route
title: Square the two-by-two arrow involution and conjugate its source block
target: murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness
requires: []
---

Using `(MSC1)`, direct block multiplication gives

```text
W^2=[[ (1-a)^2+sbar s,
       (1-a)sbar+sbar(1-d)],
     [ s(1-a)+(1-d)s,
       s sbar+(1-d)^2 ]]
   =[[1,0],[0,1]].
```

Also

```text
W diag(a,0)=[[0,0],[s,0]],
```

and right multiplication by `W` gives `diag(0,ssbar)=diag(0,d)`.
The standard identity `diag(g,g^(-1)) in E_2(R)` for an invertible matrix
`g` (after viewing its entries in the stabilized matrix ring) supplies a
finite elementary word.  Steinberg conjugation then transports the named
root subgroup exactly.
