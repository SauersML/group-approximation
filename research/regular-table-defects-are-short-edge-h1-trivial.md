---
rg: 2
id: regular-table-defects-are-short-edge-h1-trivial
kind: claim
title: Regular-table defects are trivial in the short-edge H1 coefficient system
distinct_from:
  short-edge-gauge-torsor-h1-vanishes: that theorem quantitatively bounds a local trivialization once the local H1 class is trivial; this claim supplies that local triviality for the special defects produced by regular-character table shadows.
  ambient-h1-triviality-need-not-be-short-edge-local: that firewall shows the ambient correction available for every permutation table is insufficient by itself, so the special regular-table geometry is load-bearing here.
---

For every fixed finite regular-character multiplication table `T`, the
relation defects produced by sufficiently tight simultaneous spherical shadow
matchings define the trivial class in the nonabelian `H^1` obstruction set
whose coefficients are the geometrically short-edge permutations of the
cloud, after discarding the already charged exceptional roots.

Equivalently, the exact relations among relations of `T` admit null-fillings
inside the local coefficient system, not merely after inclusion into the full
symmetric group.  The bound on the filling length may depend on `T`, but not
on the cloud size or matrix dimension.

This is the missing input exposed by
`ambient-h1-triviality-need-not-be-short-edge-local`.  Ambient triviality
follows formally from the existence of the uncorrected permutation table;
local triviality does not.
