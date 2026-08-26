---
rg: 2
id: titz-witzel-mapping-tori-are-virtually-products
kind: claim
title: Every Titz--Witzel simple-lattice mapping torus is virtually a product
distinct_from:
  titz-witzel-simple-kazhdan-cat0-lattices-exist: That imports finite presentation, torsion-freeness, simplicity and property (T); this computes the outer automorphism groups and classifies all cyclic mapping tori of those lattices.
  finite-outer-order-mapping-torus-is-virtually-product: That is the abstract implication from finite outer order; this proves the hypothesis and explicit divisibility bounds for each of the five Titz--Witzel lattices.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: That asks for an extrinsically created radical; this proves that no genuinely extrinsic cyclic action exists for these candidate kernels.
artifacts:
  - research/artifacts/torsion-free-exact-radical-team-audit-2026-08-26.md
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
---

Let `K` be one of the five simple finite-index subgroups of the Titz
Mite--Witzel `C2`-tilde lattices, acting on its exotic Euclidean building `X`.
Then `Out(K)` is finite.  More precisely, its order divides the corresponding
entry in

```text
2, 32, 32, 64, 64.                                    (TWO2)
```

Consequently every automorphism mapping torus

```text
G_phi = K semidirectProduct_phi Z
```

has a finite-index subgroup isomorphic to `K x Z`.  In particular,

```text
G_phi is MF  iff  K is MF.                             (TWO3)
```

In fact `K` is unconditionally non-MF and
`Rad_MF(K)=K` by `simple-kazhdan-groups-have-full-mf-radical`.  Hence for
every `phi`,

```text
Rad_MF(G_phi)=K x {0},       G_phi/Rad_MF(G_phi) ~= Z. (TWO4)
```

Thus this candidate family solves
`torsion-free-sofic-exact-mf-radical-over-z` if and only if at least one of
the five kernels is sofic.  In that event `phi=id` already
works, and the preferred strengthening holds because `K` is finitely
presented and every nonidentity element normally generates the simple group.
Soficity is currently not established for these lattices; non-MF is settled.
