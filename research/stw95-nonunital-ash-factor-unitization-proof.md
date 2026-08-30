---
rg: 2
id: stw95-nonunital-ash-factor-unitization-proof
kind: route
title: Unitize the ASH factor and pass purity to the tensor ideal
target: stw95-nonunital-ash-factor-preserves-purity
requires: []
---

First suppose that `L` is an ideal in a unital separable ASH algebra `D`.
Seth--Vilalta, *Continuous functions over a pure C-star algebra*, Theorem B
(Theorem 6.7), gives

```text
A tensor_min D  is pure.
```

The injectivity of the minimal tensor product embeds `A tensor_min L` into
`A tensor_min D`.  Its image is a closed two-sided ideal: this is immediate
on elementary tensors from `DL+LD subset L` and then follows on taking norm
closures.  This assertion does not identify the ideal with the kernel of a
tensor quotient map and therefore does not require `A` to be exact.

Pureness passes to closed ideals.  Hence `A tensor_min L` is pure.

Now let `L` be an arbitrary separable ASH algebra.  If it is unital, use
Seth--Vilalta directly.  If it is nonunital, its minimal unitization
`L_tilde` is again a unital separable ASH algebra: unitizing a subhomogeneous
inductive system yields a unital subhomogeneous inductive system with limit
`L_tilde`.  Apply the preceding ideal argument to

```text
L ideal L_tilde.
```

This proves the theorem without extending any step of the Seth--Vilalta
argument itself beyond its stated unital hypothesis.
