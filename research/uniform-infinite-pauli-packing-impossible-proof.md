---
rg: 2
id: uniform-infinite-pauli-packing-impossible-proof
kind: route
title: Take a convergent subsequence in the compact unitary group
target: uniform-infinite-pauli-packing-impossible
requires: []
---

The compact metric space `U(d)` contains a convergent subsequence
`A_(i_k)->A`.  Along two disjoint tails,

```text
A_(i_(2k)) A_(i_(2k+1)) + A_(i_(2k+1)) A_(i_(2k)) -> 2A^2.
```

Normalized Hilbert--Schmidt norm is continuous and `A^2` is unitary, so the
norm of the limit is exactly `2`.  This contradicts `(UIP1)` when
`epsilon<2`.

