---
rg: 2
id: sequential-marginal-holonomy-proof
kind: route
title: Decompose over the joint frozen-marginal atoms
target: sequential-marginal-holonomy-is-conditional-rank-matching
requires: []
---

The projections `(e_omega)_omega` are pairwise orthogonal and sum to the
identity.  A unitary commutes with every `d_i` if and only if it is block
diagonal for this decomposition.

Because `y` and `z` commute with the `d_i`, their positive and negative
spectral projections are block diagonal as well.  If `(CMH2)` holds, its
restriction to `e_omega C^D` unitarily conjugates the two spectral
decompositions, so the two ranks in `(CMH3)` agree.

Conversely, assume `(CMH3)`.  On each block `e_omega C^D`, choose a unitary
which maps the positive spectral subspace of `y` to that of `z` and the
negative spectral subspace of `y` to that of `z`.  Their orthogonal direct
sum commutes with all `e_omega`, hence with every `d_i`, and conjugates `y`
to `z`.  This proves the equivalence.

For a diagonal context algebra, multiplying the atom decomposition by
`e_omega` gives exactly the conditional assignment fibers described in the
claim.  If every fiber is a single context atom, the commutant of all
`e_omega` is block diagonal on those atoms, so conjugation fixes each atom
projection.
