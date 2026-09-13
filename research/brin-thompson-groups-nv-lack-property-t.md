---
rg: 2
id: brin-thompson-groups-nv-lack-property-t
kind: claim
title: "No Brin-Thompson group nV (n >= 2) has Kazhdan's property (T)"
---

For every `n >= 2`, the Brin–Thompson group `nV` does not have property (T):
it has an isometric affine action on a Hilbert space without a fixed point,
or equivalently a unitary representation with almost invariant vectors and no
invariant vector.

This is the "no" answer to the (T) part of Zaremsky Problem 2.7
(`zaremsky-2-07-brin-thompson-nv-haagerup-or-t`). Property (T) does not pass to
subgroups or overgroups, so the claim is per `n`.

## Attempts

- **From a-T-menability.** Immediate from `brin-thompson-groups-nv-are-a-t-menable`
  (route `brin-thompson-nv-lack-property-t-from-a-t-menability`).
- **Amenable action without finite orbits.** A (T) group acting on a set with
  an invariant mean has a finite orbit. Candidate `nV`-sets are orbits of
  points of `C^n` and coset spaces of fibration stabilizers
  `LC(C, V) ⋊ V`. For `V` on the orbit of an aperiodic point, the level
  function `|u| - k` of `u σ^k x` changes by bounded amounts but the level sets
  grow like `2^level`, so level-band Følner candidates fail by a constant
  fraction. No amenable candidate yet.
- **Unbounded commensurating action.** Any commensurated subset with unbounded
  `|gA Δ A|` would do (no FW, hence no (T)). The action must be
  infinite-dimensional, by `FW_infinity`.
