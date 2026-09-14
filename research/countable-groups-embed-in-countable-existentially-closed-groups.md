---
rg: 2
id: countable-groups-embed-in-countable-existentially-closed-groups
kind: claim
title: Every countable group, and every countable torsion-free group, embeds in a countable existentially closed group of the same kind
distinct_from:
  local-approximation-properties-are-marked-closed: that is about the topology of the failure locus of a local approximation property; this is the existence of the model-theoretic universal objects used to test such properties.
---

**ESTABLISHED** through `countable-ec-overgroup-union-of-chains-proof`.
Elementary and standard; no novelty is claimed.

**Definitions.**  Let `X` be either the class of all groups or the class of
torsion-free groups.  A group `H` in `X` is **`X`-existentially closed**
(`X`-e.c.) if every finite system of equations and inequations in finitely
many unknowns, with constants from `H`, that has a solution in some group of
`X` containing `H`, already has a solution in `H`.  For `X` = all groups this
is the usual notion of an existentially closed group.

**Statement.**  For `X` either class, every countable group `G` in `X` embeds
in a countable `X`-e.c. group.  In particular countable `X`-e.c. groups exist
(start from the trivial group).
