---
rg: 2
id: stw63-coordinatewise-product-uniqueness-proof
kind: route
title: Choose implementing unitaries independently with one uniform tolerance
target: stw63-uniqueness-is-closed-under-products
requires: []
---

Let `phi,psi:Z->product_j B_j` be unital embeddings, and let
`phi_j,psi_j` be their coordinate maps.  Each coordinate map is unital and
therefore injective because `Z` is simple.

Fix a finite set `F subset Z` and `epsilon>0`.  For every `j`, coordinatewise
uniqueness supplies a unitary `u_j in B_j` satisfying

```text
max_(z in F) ||u_j phi_j(z)u_j* - psi_j(z)|| < epsilon.
```

Then `u=(u_j)` is a unitary in the product, and the product norm gives

```text
max_(z in F) ||u phi(z)u* - psi(z)|| <= epsilon.
```

Directing the pairs `(F,epsilon)` by inclusion and decreasing tolerance, or
using a dense sequence and diagonalizing, gives a sequence of product
unitaries implementing approximate equivalence on all of `Z`.
