---
rg: 2
id: scalar-reynolds-minimal-os-proof
kind: route
title: Use minimality of the diagonal-masa operator space
target: scalar-reynolds-cb-norm-is-the-infinity-norm
requires: []
---

Every complex subspace of a commutative `C*`-algebra carries the minimal
operator-space structure.  For any operator space `X` and bounded map
`T:X->MIN(E)`, the defining mapping property gives `||T||_cb=||T||`.

With the maximum direct-sum norm on the two output rows, `ran(C_Q)` is an
operator subspace of a commutative algebra and the kernel complement is a
complex subspace of `l_infinity(<R>\Q)`, hence minimal.  Apply the mapping
property to the range-restricted Moore--Penrose inverse.  Its matrix
amplifications are exactly the matrix-valued diagonal functions, proving the
displayed cb/infinity equality.  The anti-Hermitian tangent is only the real
form and inherits the bound by restriction.
