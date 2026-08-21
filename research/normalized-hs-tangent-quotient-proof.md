---
rg: 2
id: normalized-hs-tangent-quotient-proof
kind: route
title: Put an anticommuting Pauli pair on a vanishing-rank block
target: normalized-hs-tangent-quotient-is-nonabelian
requires: []
---

Choose even `r_n<=d_n` with `f_n=r_n/d_n->0` and put
`epsilon_n=sqrt(f_n)`. On an `r_n`-dimensional reducing block let `A_n` and
`B_n` be direct sums of the Pauli matrices `X` and `Z`; let both be the
identity on the orthogonal complement. The Pauli matrices are traceless
self-adjoint involutions and anticommute. Therefore

```text
||A_n-I||_2^2=2f_n,
||B_n-I||_2^2=2f_n,
[A_n,B_n]=-I on the active block and I off it,
||[A_n,B_n]-I||_2^2=4f_n.
```

This proves `(NHT1)`: the commutator is not `o(epsilon_n)`, so the tangent
classes of `A_n` and `B_n` do not commute.

For the positive boundary, unitary invariance and

```text
AB-BA=(A-I)(B-I)-(B-I)(A-I)
```

give

```text
||[A,B]-I||_2=||AB-BA||_2
 <=||A-I||_op ||B-I||_2+||B-I||_op ||A-I||_2.
```

The stated operator-diffuse assumptions make the right side
`o(epsilon_n)`.
