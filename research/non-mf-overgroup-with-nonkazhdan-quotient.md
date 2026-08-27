---
rg: 2
id: non-mf-overgroup-with-nonkazhdan-quotient
kind: claim
title: A non-MF subgroup and a non-Kazhdan quotient make the ambient group non-MF and non-Kazhdan
distinct_from:
  non-mf-times-infinite-cyclic-is-non-mf-and-nonkazhdan: that is the direct-product specialization with quotient Z; this permits an arbitrary overgroup and an arbitrary non-Kazhdan quotient and includes free products as well.
  torsion-free-finitely-presented-non-mf: that constructs a new non-MF group with controlled torsion; this only transports two already known properties through subgroup and quotient maps.
artifacts:
  - research/artifacts/property-t-free-provenance-delta-2026-08-26.md
---

Let `G` contain a subgroup `B` which is not operator-MF, and suppose there is
a surjection

```text
G -> A
```

onto a group `A` without Property `(T)`.  Then `G` is not operator-MF and
does not have Property `(T)`.

Two useful specializations are:

1. if `B` is non-MF and `A` is non-Kazhdan, then `B x A` is non-MF and
   non-Kazhdan;
2. under the same hypotheses, `B * A` is non-MF and non-Kazhdan.

Finite generation and finite presentation are preserved in both
specializations when the two factors have the corresponding property.

This is a structural wrapper, not an independent Property-`(T)`-free proof
of the seed's non-MF property.  Any hypothesis used to prove `B` non-MF
remains in the proof provenance after applying the wrapper.

DERIVATION
non-mf-overgroup-with-nonkazhdan-quotient-proof
