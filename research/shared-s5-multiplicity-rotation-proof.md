---
rg: 2
id: shared-s5-multiplicity-rotation-proof
kind: route
title: Rotate the two trivial summands in the restricted permutation representation
target: shared-s5-selector-face-has-multiplicity-rotation-gauge
requires: []
---

The subgroup `H` fixes `e_i` and permutes the other five basis vectors.
Hence it fixes both `e_i` and their normalized sum `v`, and acts as the
four-dimensional standard representation on the orthogonal complement.
This proves `(SMG2)` and shows that the swap `U` belongs to `rho(H)'`.
Therefore the two representations in `(SMG3)` have identical restrictions
to `H`.

They differ on `x=(i p)` because `U` does not commute with `rho(x)`.  For
example,

```text
U rho(x)e_i=Ue_p
```

has coefficient `4/5` at `e_p`, whereas

```text
rho(x)Ue_i=rho(x)v
```

has coefficient zero at `e_p`.  Thus `(SMG4)` holds.

Finally `x` fixes every letter in `Delta={j,k,l,q}`, so it centralizes
`K=Sym(Delta)`.  Since `U` commutes with `rho(K)`, both `rho_0(x)` and
`rho_1(x)` commute with the same matrices `rho(K)`.  All elements supported
in `H` have identical matrices in the two extensions.  This proves every
asserted exact local relation and the surviving multiplicity gauge.

