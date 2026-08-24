---
rg: 2
id: e5-two-pair-extraspecial-cell-proof
kind: route
title: Use two transverse A2 root triangles and finite Stone-von Neumann
target: e5-idempotent-root-has-two-pair-extraspecial-cell
requires: []
---

The Steinberg relation

```text
[x_ij(r),x_jk(s)]=x_ik(rs)
```

gives both identities in `(ETC2)`, because the relevant products are
`a^2=a`.  The root-index commutator criterion shows that

```text
[X_1,X_2]=[X_1,Y_2]=[Y_1,X_2]=[Y_1,Y_2]=1.
```

It also shows that `Z=x_13(a)` commutes with all four generators.  Root
additivity in characteristic `p` gives the exponent relations.  This proves
the quotient map from `(ETC3)`.

Fix a nontrivial central character `Z mapsto zeta`.  The finite
Stone--von Neumann theorem gives one irreducible representation with that
central character, of dimension `p^2`; every representation of the central
sector is its tensor product with a multiplicity space.  In the standard
Schrodinger model on `l2(F_p^2)`, take `X_1,X_2` as the two commuting
translations.  Their joint Fourier transform has `p^2` one-dimensional
character spaces.  Tensoring by the multiplicity space proves `(ETC5)`.

The commutant of the irreducible packet on this sector is
`I tensor B(M)`.  Therefore a packet-reducing projection has the form
`I tensor P_0`, and intersecting it with any joint `(X_1,X_2)` character
projection divides its trace by `p^2`.  This proves `(ETC6)`.

The robust statement uses only a fixed finite group: normalized-HS
finite-group stability exactifies the packet, and averaging over it moves an
approximately central projection into `I tensor B(M)` with fixed linear
loss.  The exact trace calculation then applies.

