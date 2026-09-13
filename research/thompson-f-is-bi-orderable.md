---
rg: 2
id: thompson-f-is-bi-orderable
kind: claim
title: Thompson's group F is bi-orderable
distinct_from:
  lodha-moore-group-is-bi-orderable-and-not-lea: that orders the piecewise projective Lodha--Moore group and adds that it is not LEA; this orders the piecewise linear group F, whose soficity is the open claim thompson-f-is-not-sofic.
---

**ESTABLISHED.**  Realize Thompson's group `F` as the group of
orientation-preserving piecewise linear homeomorphisms of `[0,1]` with finitely
many breakpoints, all dyadic, and slopes in `2^Z` (Cannon--Floyd--Parry,
*Introductory notes on Richard Thompson's groups*).  Then `F` carries a total
order invariant under both left and right multiplication.  In particular `F`
is left-orderable and torsion-free.

This is classical, and no novelty is claimed.  It is recorded as a node so
that `left-orderable-non-sofic-via-thompson-f` can consume it.

The order is the germ order at the leftmost moved point, the same order that
`lodha-moore-group-is-bi-orderable-and-not-lea-proof` uses for piecewise
projective maps.

Derivation: `thompson-f-is-bi-orderable-proof`.
