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

For the finite estimate, compare two distinct members:

```text
2=||2A_i^2||_2
 <= ||A_iA_j+A_jA_i||_2
    +||A_i(A_i-A_j)||_2+||(A_i-A_j)A_i||_2
 <= epsilon+2||A_i-A_j||_2.
```

Hence their normalized-HS distance is at least `rho=1-epsilon/2`.  Regard
`M_d(C)` as a real Euclidean space of dimension `2d^2`; all unitaries lie in
its unit ball.  The open balls of radius `rho/2` around the `A_i` are disjoint
and lie in the ball of radius `1+rho/2`.  Comparing Euclidean volumes gives

```text
|I| (rho/2)^(2d^2) <= (1+rho/2)^(2d^2),
```

which is `(UIP2)`.
