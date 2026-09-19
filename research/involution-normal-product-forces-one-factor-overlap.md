---
rg: 2
id: involution-normal-product-forces-one-factor-overlap
kind: claim
title: A bounded normal product of involutions overlaps one factor carrier
artifacts:
  - research/telescoping-involution-product-overlap-proof.md
---

Let `r,v_1,...,v_k` be self-adjoint involutions in a finite tracial von
Neumann algebra, put

```text
q=(1-r)/2,                    p_j=(1-v_j)/2,
w=v_1...v_k,
```

and suppose `||r-w||_2<=eta`.  Then

```text
sum_(j=1)^k tau(q p_j)
  >= (max{sqrt(tau(q))-eta/2,0})^2/k,                 (NPO1)
```

and hence some `j` satisfies

```text
tau(q p_j)
  >= (max{sqrt(tau(q))-eta/2,0})^2/k^2.              (NPO2)
```

In particular, if `r` is exactly a product of `k` conjugates of one
self-adjoint involution `z`, the nontrivial spectral carrier of `r` has
overlap at least `tau(q)/k^2` with one conjugate of the nontrivial spectral
carrier of `z`.

The conclusion is purely finite-dimensional/tracial.  It uses neither
Property T nor a stability theorem.  It does not select one factor uniformly
over a family of products: the successful index and conjugating word may
depend on the product.

DERIVATION
telescoping-involution-product-overlap-proof
