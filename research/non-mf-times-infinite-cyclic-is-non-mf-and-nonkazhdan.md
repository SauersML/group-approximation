---
rg: 2
id: non-mf-times-infinite-cyclic-is-non-mf-and-nonkazhdan
kind: claim
title: A non-MF group times the infinite cyclic group remains non-MF and is not Kazhdan
distinct_from:
  hs-collapse-sign-twist-non-mf: that constructs a new marked HNN group from an HS-collapse certificate; this uses only subgroup heredity of MF and the direct-product quotient onto the infinite cyclic group.
  torsion-free-finitely-presented-non-mf: that supplies a specific torsion-free non-MF construction; this is a general wrapper for any non-MF seed and makes no claim that the seed's proof avoided Kazhdan input.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

Let `B` be a countable non-MF group.  Then

```text
G=B x Z
```

is countable, non-MF, and does not have property `(T)`.  Finite generation
and finite presentation pass from `B` to `G`.

This removes property `(T)` from the resulting group's structure, not
necessarily from the provenance of the non-MF theorem for `B`.  If the only
known proof for the seed uses a Kazhdan mechanism, the product construction
does not create an independent analytic obstruction.

