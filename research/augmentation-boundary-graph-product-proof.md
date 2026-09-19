---
rg: 2
id: augmentation-boundary-graph-product-proof
kind: route
title: Combine the Kazhdan Cayley gradient with a finite-difference graph-product model
target: augmentation-boundary-expands-but-not-products
requires: []
---

The Cayley graph of `(A,S)` is connected.  Every even finite subset of its
vertices is therefore the mod-`2` boundary of a finite edge chain: pair its
vertices and sum paths joining each pair.  This proves surjectivity in
`(ABE1)`, while equivariance and degree two are immediate.

The left regular representation of infinite `A` has no invariant vector.
Apply the Kazhdan inequality for `S` to `xi in ell^2(A)`.  After weakening
`max_s` to the sum, it gives `(ABE3)` (with the chosen convention for
`kappa`).

For the product-table obstruction, let the finitely many prototype lamp
words have supports `F_1,...,F_r subset A`.  Put

```text
D=union_i F_i^(-1)F_i.
```

Form the left-`A`-invariant graph on vertex set `A` by joining `g` and `h`
whenever `g^(-1)h` lies in `D` or its inverse, and let `K_D` be the graph
product with one vertex group `C_2=<c_g>` at each `g`.  Every translate
`aF_i` spans a clique.  Its vertex lamps therefore commute, so every listed
word, being valid in the abelian lamp group, is trivial in `K_D`.  Left
translation acts by graph automorphisms and gives the semidirect product
`(ABE4)`.

The set `D` is finite and `A` is infinite.  Choose `r notin D`; then `c_e`
and `c_r` are nonadjacent vertex generators and do not commute in the graph
product normal form.  On the other hand all boundary elements
`c_g c_(gs)` exist as ordinary words, and every finitely listed linear path
or parity identity is among the clique-supported relations once its finite
support is included in the prototypes.  Thus the bounded-degree linear
boundary presentation and every fixed local checksum can be exact while the
global elementary-abelian product table fails.  This proves the claim.

