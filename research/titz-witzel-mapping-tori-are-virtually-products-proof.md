---
rg: 2
id: titz-witzel-mapping-tori-are-virtually-products-proof
kind: route
title: Apply Euclidean-building rigidity and finite-index simplicity
target: titz-witzel-mapping-tori-are-virtually-products
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
  - finite-outer-order-mapping-torus-is-virtually-product
  - mf-radical-product-and-restricted-sum-formulas
  - simple-kazhdan-groups-have-full-mf-radical
---

Titz Mite--Witzel, *Non-residually finite C2-tilde-lattices*,
arXiv:2509.05054v2, compute that `K` has finite index in `Aut(X)`.  Combining
their displayed indices gives

```text
[Aut(X):K] = 2, 32, 32, 64, 64                       (TWO5)
```

for the five simple subgroups.

Every automorphism `alpha` of `K` induces an `alpha`-equivariant
quasi-isometry of `X`, because `K` acts properly and cocompactly.  The
Euclidean-building rigidity theorem quoted in the paper (Kleiner--Leeb,
Theorem 1.1.3, with Leeb's removal of the Moufang hypothesis) supplies a
unique building isometry `F` at bounded distance from that quasi-isometry.
Equivariance gives

```text
F k F^(-1) = alpha(k)
```

for every `k in K`.  Hence `F` normalizes `K`, and conjugation maps the
normalizer onto `Aut(K)`.

Conversely, `K` is finite index in `Aut(X)`.  For any `a in Aut(X)`, the
intersection `K intersect aKa^(-1)` has finite index in the infinite simple
group `K`.  An infinite simple group has no proper finite-index subgroup:
the core of one would be a proper finite-index normal subgroup.  Thus the
intersection is `K`, and the symmetric argument gives `aKa^(-1)=K`.
Therefore the normalizer is all of `Aut(X)`.  Modulo inner automorphisms, the
surjective conjugation map shows that `Out(K)` is a quotient of
`Aut(X)/K`.  Its order is consequently finite and divides the corresponding
index in `(TWO5)`, proving `(TWO2)`.

Now apply `finite-outer-order-mapping-torus-is-virtually-product` to every
`phi`.  This gives the finite-index copy of `K x Z`.  MF is invariant under
finite index and obeys the direct-product formula, proving `(TWO3)`.

By `simple-kazhdan-groups-have-full-mf-radical`, the infinite simple Kazhdan
group `K` is non-MF, every homomorphism from `K` to an MF group is trivial,
and `Rad_MF(K)=K`.  Therefore the restriction to `K` of every homomorphism
`G_phi->M` with `M` MF is trivial, so `K<=Rad_MF(G_phi)`.  The quotient
homomorphism `G_phi->Z` gives the reverse inclusion.  This proves `(TWO4)`
directly, independently of the finite-index product calculation.

Soficity passes to subgroups and is preserved under extensions with amenable
quotient.  Thus `G_phi` is sofic exactly when `K` is sofic.  This proves the
corrected final equivalence: one Titz--Witzel mapping torus solves the target
if and only if its simple kernel is sofic; non-MF needs no additional input.
