---
rg: 2
id: simple-kazhdan-groups-have-no-proper-co-amenable-subgroups
kind: claim
title: An infinite simple Kazhdan group has no proper co-amenable subgroup
distinct_from:
  no-invariant-mean-on-coset-space: that says a Kazhdan group has no invariant mean on an infinite coset space, so co-amenable subgroups have finite index; this adds simplicity and infinitude to conclude that the only co-amenable subgroup is the group itself, the form an entropy induction on a canonical host consumes.
  kun-thom-stabilizer-not-co-amenable: that excludes co-amenability for one specific Kun--Thom stabilizer; this excludes every proper subgroup of every infinite simple Kazhdan group.
artifacts:
  - research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md
---

Let `G` be an infinite simple group with property (T), and let `H <= G` carry a `G`-invariant mean on `G/H`. Then `H = G`.

This is Proposition 1.1 of the artifact. `no-invariant-mean-on-coset-space` makes `[G:H]` finite. The kernel of the action on the finite set `G/H` is a normal subgroup of finite index. By simplicity it is `G`, since it cannot be trivial in an infinite group. So `H = G`.

**Why it is recorded.** Lower bounds for Rokhlin entropy that are induced from an entropy theory on a subgroup `H` (amenable, sofic, or free through the f-invariant) need Følner sets for `G` acting on `H\G`, that is, co-amenability of `H`. On the canonical INF hosts of `rokhlin-maximality-via-fg-simple-kazhdan-hosts` the only such `H` is `G`, so these inductions return the question unchanged. The mechanism analysis is Sections 1.2, 2.3 and 3 of the artifact. It is not part of this claim.
