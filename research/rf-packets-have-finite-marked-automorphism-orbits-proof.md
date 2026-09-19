---
rg: 2
id: rf-packets-have-finite-marked-automorphism-orbits-proof
kind: route
title: Intersect all subgroups up to one separating index
target: rf-packets-have-finite-marked-automorphism-orbits
requires: []
---

Choose a finite quotient separating `y`, let `N` be its kernel, and put
`m=[Gamma:N]`.  A finitely generated group has only finitely many subgroups
of any given finite index: an index-`k` subgroup is a point stabilizer for one
of finitely many homomorphisms from a fixed finite generating set to
`Sym(k)`.  Hence

```text
C=intersection {H<=Gamma:[Gamma:H]<=m}
```

has finite index.  Automorphisms preserve index and permute this finite
family, so `C` is characteristic.  Since `N` occurs in the intersection,
`C<=N` and `y` survives in the finite quotient `Q=Gamma/C`.

The given actor descends to `Aut(Q)`, producing the finite marked quotient

```text
Gamma rtimes B -> Q rtimes image(B->Aut(Q)).
```

Finally, faithfulness of the regular representation of `Q` supplies an
irreducible representation which does not kill `q(y)`.  Its pullback has a
finite `B`-orbit inside the finite dual of `Q`, proving the equivalent type
formulation.
