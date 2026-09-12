---
rg: 2
id: finite-predicate-signed-permutation-sector-proof
kind: route
title: Use the full diagonal sign group and a transitive coordinate cycle
target: finite-predicate-signed-permutation-sector
requires: []
---

Let `D` be the full group of diagonal sign matrices on `C^S`, and let `z` be a
cycle through all basis vectors.  The generated group `H_S=<D,z>` is a finite
subgroup of the signed permutation group.  If `W` is invariant under `H_S`, it
is invariant under `D`.  The coordinate projections are linear combinations
of elements of `D`, so `W` is a sum of coordinate lines.  Invariance under the
transitive cycle `z` then forces `W=0` or `W=C^S`.  The natural representation
is irreducible.

For each input coordinate `i`, the diagonal matrix `X_i` with entry `s_i` on
`e_s` belongs to `D`, and the `X_i` commute and square to one.  The joint
eigenvalue tuple on `e_s` is exactly `s`; since `S` is a set, these tuples are
distinct.  Hence the joint spectrum, with multiplicity one, is precisely `S`.

