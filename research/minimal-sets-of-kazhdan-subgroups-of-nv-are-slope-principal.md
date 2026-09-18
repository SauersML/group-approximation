---
rg: 2
id: minimal-sets-of-kazhdan-subgroups-of-nv-are-slope-principal
kind: claim
title: For every subgroup K of nV with property (T), no element of K fixes a point of a minimal closed K-invariant set with nonzero slope
distinct_from:
  minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures: that asks for invariant measures on minimal sets; this asks only that fixed points in minimal sets have zero slope, a pointwise germ condition that finite Kazhdan subgroups satisfy automatically.
  nv-point-germ-groups-embed-in-zn-by-slope: that proves slope zero for fixed points of Kazhdan stabilizers (finite-index or otherwise with (T)); this asks it for every element of K fixing a point of a minimal set, where the stabilizer has infinite index.
  some-hyperbolic-group-does-not-embed-in-thompson-v: that excludes Kazhdan hyperbolic groups from V through the Haagerup property; this is the germ-level statement for nV that a Kazhdan boundary-type action would violate.
---

Let `n >= 1` and `K <= nV` have property (T). Let `Z ⊆ C^n` be a minimal closed
`K`-invariant set, `g ∈ K` and `z ∈ Z` with `gz = z`. Then `s(g,z) = 0`.

## Status

OPEN. Implied by `kazhdan-subgroups-of-brin-thompson-groups-are-finite`: if `K` is
finite, `Z` is a finite orbit and `Stab_K(z)` has finite index, hence (T), and item 6 of
`nv-point-germ-groups-embed-in-zn-by-slope` gives slope zero. It holds for `n = 1`
through `thompson-v-has-haagerup-property`.

## What a counterexample looks like

By items 4 and 5 of `nv-point-germ-groups-embed-in-zn-by-slope`, a failure is an
infinite minimal `Z ⊆ Z_K` together with an element `g ∈ K` that either:
- compresses a brick meeting `Z` canonically into itself (constant-sign slope), or
- has a saddle fixed point in `Z` (mixed-sign slope, `n >= 2`).

This is the germ picture of a loxodromic element acting on a Cantor model of the
boundary of a hyperbolic Kazhdan group. So a counterexample to this claim is the
first dynamical step of a construction toward
`zaremsky-2-19a-every-hyperbolic-group-in-some-nv-resolved` for Kazhdan hyperbolic
groups.

## Where (T) must enter

Ping-pong free subgroups of `V` have compressing fixed points on their minimal sets.
Cocompact lattices in `Sp(k,1)` act on horofunction-boundary Cantor models with cyclic
point stabilizers, so the germ invariant alone (abelian of rank at most `n`) does not
exclude them (standard facts, not re-read at source). A proof must use the slope
values, not only the shape of the germ group.
