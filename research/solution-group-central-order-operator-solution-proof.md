---
rg: 2
id: solution-group-central-order-operator-solution-proof
kind: route
title: Cut the regular representation by the central phase character
target: solution-group-central-order-is-operator-solvability
requires: []
---

An operator solution sends `J` to a primitive `p`th root of unity and hence
forces full order.  Conversely, when `J` has order `p`, its cyclic subgroup
acts regularly inside the left regular representation.  The Fourier
idempotent for the character `J |-> omega_p` is therefore nonzero.  Since `J`
is central, that spectral subspace is invariant under the entire solution
group.  Restricting the regular representation to it sends `J` to
`omega_p I`, and the solution-group presentation is exactly the operator-
solution system.
