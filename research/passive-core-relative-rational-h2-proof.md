---
rg: 2
id: passive-core-relative-rational-h2-proof
kind: route
title: Compute both amalgam Mayer--Vietoris sequences and the mapping cone
target: passive-core-quotient-has-relative-rational-h2
requires:
  - iwahori-square-root-presentation-is-bs14-plus-one-involution
---

The established square-root presentation identifies the exact passive core
as

```text
BS(1,4) *_(<R>) D_infinity
```

and identifies the quotient map with attachment of exactly the two cubic
rows.  Rational Mayer--Vietoris for this amalgam gives zero `H_1` and
`H_2`: the edge `H_1` maps isomorphically to the sole rational vertex
summand, and the following connected-components map is injective.

Independently, apply rational Mayer--Vietoris to the Bruhat--Tits amalgam

```text
PSL_2(Z[1/2])
  = PSL_2(Z) *_(Gamma_0(2)) PSL_2(Z).
```

The vertices have zero rational `H_1` and `H_2`, whereas
`Gamma_0(2)=C_2*Z` has one-dimensional rational `H_1`.  Thus the quotient
has `H_2=Q` and `H_1=0`.  The mapping-cone exact sequence then identifies
`H_2(Cone(Bq),Q)` with `Q`.  This is one relative topological class; no
matrix countersequence or Hilbert--Schmidt obstruction is inferred.
