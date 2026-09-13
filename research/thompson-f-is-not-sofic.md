---
rg: 2
id: thompson-f-is-not-sofic
kind: claim
title: Thompson's group F is not sofic
refuted_by:
  - thompson-f-is-sofic
distinct_from:
  thompson-f-is-not-amenable: that is nonamenability, which a sofic F could satisfy; this is the stronger statement that F has no sofic approximations, which implies it.
  thompson-v-not-sofic: that is nonsoficity of V, which this claim implies because F <= V; the converse is not known.
  thompson-f-relator-system-stable-in-permutations: that is the finitary permutation form posed by Arzhantseva and Paunescu; this is the group statement, equivalent to it.
---

**OPEN.** Thompson's group `F` admits no sofic approximation.

**Equivalent forms** (`thompson-f-sofic-iff-relator-system-unstable`):
- the two relators of `F` are stable in permutations;
- almost-solutions of the two relators almost commute, uniformly in the size;
- `F` is permutation stable.

**Consequences.** This claim makes `V` nonsofic (`thompson-v-not-sofic-from-f-not-sofic`) and `F`
nonamenable. It would give a nonsofic group with the Haagerup property, so no Kazhdan compression
mechanism can prove it (`a-t-menable-groups-have-no-rigid-compression-defect`).
