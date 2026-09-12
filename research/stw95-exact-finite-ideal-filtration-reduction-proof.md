---
rg: 2
id: stw95-exact-finite-ideal-filtration-reduction-proof
kind: route
title: Tensor the filtration exactly and apply extension permanence cell by cell
target: stw95-exact-finite-ideal-filtration-reduction
requires: []
---

Exactness of `B` gives, for each `k`, a short exact sequence

```text
0 -> I_{k-1} tensor_min B -> I_k tensor_min B
  -> (I_k/I_{k-1}) tensor_min B -> 0.
```

The zero algebra is pure.  Inductively, if `I_{k-1} tensor_min B` is pure,
then the hypothesis makes both ends of this extension pure.
Perera--Thiel--Vilalta's extension theorem says the middle algebra is pure.
At `k=m` this is `A tensor_min B`.
