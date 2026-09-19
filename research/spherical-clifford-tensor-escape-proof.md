---
rg: 2
id: spherical-clifford-tensor-escape-proof
kind: route
title: Tensor atomic Hecke quadrature with a conjugate-doubled coweight Folner box
target: spherical-quadrature-tensors-through-clifford-folner-windows
requires:
  - finite-spherical-moments-do-not-fold-regular-double
  - depth-two-clifford-types-form-a-finite-fiber-folner-graph
  - finite-projective-sector-groupoids-have-conjugate-absorbers
  - clifford-covariance-atlases-have-regular-flow
---

# Tensor atomic Hecke quadrature with a conjugate-doubled coweight Folner box

Take the finite atomic spherical quadrature supplied by
`finite-spherical-moments-do-not-fold-regular-double`.  Independently, take a
full finite fiber over a coweight box in the finite-fiber Clifford graph.
The regular-flow description makes every fixed transition a bounded-range
partial translation of that box.  Completing boundary arrows to permutations
costs at most twice the square root of the boundary fraction in normalized
Hilbert--Schmidt norm.

Any fixed projective Mackey cocycle is removed before this completion by the
conjugate-doubling construction in
`finite-projective-sector-groupoids-have-conjugate-absorbers`.  Consequently
all selected local cycles are exact away from the bounded boundary layer.

Tensor the quadrature carrier and the coweight-window carrier, choosing the
quadrature accuracy to tend to zero with the box size.  This makes every
cross-commutator exact, sends every selected Clifford defect to zero, and
makes the spherical moments converge to their regular values.  The nonfolded
lazy-average value converges to `43/168`, proving the target claim.

The tensor construction deliberately does not provide the omitted arithmetic
incidence identifying the two factors.  That is the precise presentation-level
extension gate left open by this route.
