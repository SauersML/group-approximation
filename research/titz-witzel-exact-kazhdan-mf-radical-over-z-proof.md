---
rg: 2
id: titz-witzel-exact-kazhdan-mf-radical-over-z-proof
kind: route
title: Take the direct product of a simple Titz--Witzel kernel with Z
target: titz-witzel-exact-kazhdan-mf-radical-over-z
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
  - simple-kazhdan-groups-have-full-mf-radical
  - titz-witzel-mapping-tori-are-virtually-products
  - universal-mf-quotient
---

Choose any of the five Titz Mite--Witzel simple finite residuals `K` and put

```text
G=K x Z.
```

The cited lattice theorem makes `K` finitely presented, torsion-free,
infinite, simple and Kazhdan.  Hence `G` is finitely presented and
torsion-free.  By `simple-kazhdan-groups-have-full-mf-radical`, every
homomorphism from `K` to an MF group is trivial.  Restricting an arbitrary
homomorphism `G->M` to `K` therefore gives

```text
K <= Rad_MF(G).
```

The projection `G->Z` has MF target, so the definition of the radical gives
the reverse inclusion `Rad_MF(G)<=K`.  This proves `(TWE1)`.  Since `K` is
nontrivial, the radical is nontrivial and `G` is non-MF.  Simplicity says
that every nonidentity `k in K` normally generates `K` already inside `K`;
because `K normal G`, the same element normally generates the radical in
`G`.

Every map `G->M` to an MF group kills `K` and therefore factors uniquely
through `G/K~=Z`, proving `(TWE2)`.  Finally, if `G` is sofic then its
subgroup `K` is sofic; conversely, if `K` is sofic then its direct product
with the amenable group `Z` is sofic.  This establishes the final
equivalence without asserting the still-open soficity clause.
