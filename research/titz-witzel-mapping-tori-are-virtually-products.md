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

**Correction (2026-09-13, lane ex-fp-kazhdan-titz-witzel).**
- The proof route requires `simple-kazhdan-groups-have-full-mf-radical`, which is refuted
  (`simple-kazhdan-lef-group-from-minimal-subshift`). So the route cannot fire.
- Of the statements below:
  - `(TWO2)` and `(TWO3)` do not use that claim.
  - `(TWO4)` and the sentence "non-MF is settled" are **unproved**. `(TWO4)` holds exactly when
    `K` is not MF, which is the open negation of `titz-witzel-residual-is-mf`.
  - If `K` is MF, it is hyperlinear by `kazhdan-mf-hyperlinear-fragment`.

The original text follows.

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

**2026-09-13.** The last two paragraphs predate the correction above. "Unconditionally non-MF"
and "non-MF is settled" should read "non-MF if `titz-witzel-residual-is-mf` fails". The family
solves the target exactly when some kernel is sofic and not MF.
