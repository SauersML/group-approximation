---
rg: 2
id: affine-clone-model-proof
kind: route
title: Realize every finite prefix tree inside a finite affine group
target: affine-clone-model-defeats-pure-thompson-prefix-error-spreading
requires: []
---

Construct `E` as the direct limit of the level spaces

```text
E_n=F_2^({0,1}^n)
```

under the injective refinement map sending a basis vector at `x` to the sum
of the two basis vectors at `x0,x1`. This proves `(ACL1)`, nonvanishing of all
tree vectors, and the level-basis statement.

The finitary general linear group is the union of finite groups
`GL(E_n')` over finite-dimensional subspaces (enlarging a subspace when
needed). Hence `H`, and therefore `E rtimes H`, is locally finite. It acts
transitively on the nonzero vectors of `E`, proving conjugacy of all `e_x`.
The additive law of the elementary abelian group `E` makes `(ACL1)` exactly
the product relation

```text
e_x=e_(x0)e_(x1),  [e_(x0),e_(x1)]=1.
```

Any finite set of tree vectors, finitary conjugators, and leaf permutations
is contained in `E_N rtimes GL(E_N)` after enlarging `N`. This is a finite
group. Its left regular representation is an exact unitary model of every
listed relation, and a nonidentity group element has normalized trace zero.
Since `e_empty!=0`,

```text
||lambda(e_empty)-I||_2^2
 =2-2 Re tr(lambda(e_empty))=2.
```
