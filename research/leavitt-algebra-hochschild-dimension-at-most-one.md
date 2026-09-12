---
rg: 2
id: leavitt-algebra-hochschild-dimension-at-most-one
kind: claim
title: The Leavitt algebra L_k(1,2) has Hochschild dimension at most one
distinct_from:
  ara-cortinas-leavitt-tensor-k-theory-vanishes: that imports regular supercoherence of L(E) and vanishing of K-theory for L ⊗ R; this is a bimodule statement, projective dimension at most one of L as an L-bimodule, which bounds global dimensions of tensor products and says nothing about coherence or K-theory.
---

**ESTABLISHED.** Let `k` be a field and `L = L_k(1,2)`. There is an exact
sequence of `L`-bimodules

```text
0 -> L ⊗_k V ⊗_k L -> L ⊗_k L -> L -> 0
```

where `V` is the two-dimensional span of the free generators and the second map
is multiplication. So `pd_(L^e) L <= 1`, that is, `L` is quasi-free in the sense
of Cuntz--Quillen.

Consumer: `leavitt-tensor-global-dimension-bound`, which turns this into the
bound `l.gl.dim(B ⊗ L^(⊗d)) <= l.gl.dim B + d`.
