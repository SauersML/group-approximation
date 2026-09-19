---
rg: 2
id: full-fold-compose-return-affine-proof
kind: route
title: Realize the two folded returns by four binary transvections
target: full-fold-compose-return-has-finite-affine-model
requires:
  - full-completeness-opposite-menu-has-finite-gl5-fusion
---

For a vector `v in V` and an actor `g in GL(V)`, the semidirect-product
commutators are

```text
[v,g]=v+g(v),                 [g,v]=g(v)+v.             (1)
```

The maps in `(FAR2)` square to the identity.  Since `C_1=A+C`,

```text
S_0(C_0)=C_0+R_0,       S_0(C_1)=C_1,
S_1(C_0)=C_0,           S_1(C_1)=C_1+R_1,
S_j(A)=A+R_j.                                           (2)
```

Equations `(1)--(2)` prove the first two commutator columns of `(FAR3)`.
Likewise `T_i(R_i)=R_i+A` and `T_i(R_(1-i))=R_(1-i)`, proving its last
column.  This verifies both matching returns and both crossed-zero returns
with the same four actor occurrences.

For the payload extension, the action of `g in GL(V)` on `Omega=V^*` is
`chi |-> chi composed with g^(-1)`.  Hence coordinate permutation sends
`D_v` to `D_(gv)`.  Pointwise multiplication and `z^2=1` give
`D_vD_w=D_(v+w)`, so the preceding calculation embeds unchanged in
`K^Omega semidirect GL(V)`.  Supporting every base occurrence of the finite
`K` packet on `{chi:chi(v)=1}` preserves its word identities
coordinatewise, and the same coordinate action transports the whole packet.
Finally some character has `chi(A)=1`, so `D_A` is nonidentity.  Regular
translation by a nonidentity finite-group element has trace zero, proving
`(FAR7)`.

