---
rg: 2
id: adjoint-supertrace-cannot-pay-hs-selection-load
kind: claim
title: Operator-space spectral mass cannot by itself pay carrier-trace HS refinement costs
---

Normalized spectral mass in the adjoint Hilbert space `H=M_d` lives at the
`d^2` scale, while a block refinement is charged at the carrier trace
`rank/d` scale.  There is no dimension-free inequality which converts the
former into the latter, even for a single spectral direction.

Concretely, a one-dimensional self-adjoint subspace of `M_d` can contain a
normalized low-energy witness whose spectral cut has trace `1/2`.  Hence its
orthogonal projection in `H` has normalized supertrace `1/d^2`, while the cut
moves order-one carrier mass.  The same scale mismatch is already visible in
the scalar kernel: `span{I}` has supertrace `1/d^2` but its support projection
has carrier trace one.

Therefore `property-t-hs-adjoint-low-spectrum-budget`, although a genuine
dimension-free spectral constraint, does **not** by itself prove
`hs-refinement-selection-load-vanishes`.  A successful global potential must
weight low-energy directions by the positive/support geometry they can carry,
or prove an algebraization theorem which packages many such directions into
cheap invariant blocks.
