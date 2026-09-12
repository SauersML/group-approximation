---
rg: 2
id: orthogonal-idempotent-stabilized-conjugacy-proof
kind: route
title: Use the row-sum and column-inclusion matrices as a partial-isometry pair
target: orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy
requires:
  - murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness
---

Multiply the two matrices in `(OSC1)`.  Orthogonality gives

```text
sbar s=[[q,qd],[dq,d]]=diag(q,d)=p,
s sbar=[[q+d,0],[0,0]]=r.
```

The four support equations in `(OSC2)` follow from the same identities.
Apply the explicit two-by-two arrow involution to `p,r,s,sbar` in the matrix
ring and flatten the resulting finite elementary word back to a stabilized
elementary group over `R`.
