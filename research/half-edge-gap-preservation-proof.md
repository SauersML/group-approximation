---
rg: 2
id: half-edge-gap-preservation-proof
kind: route
title: Coarsen the half-edge packet back to the original BCS
target: half-edge-gauges-preserve-fanizza-gap
requires: []
---

For every half-edge impose commuting shares `A_hB_h=X_x`.  Forgetting shares
then returns the original logical representation.  Conversely, any original
representation extends using incidence-private Pauli factors and
`B_h=X_xA_h`, so exact logical models are unchanged.

In an exactified context packet, sum its joint projections over support-menu
labels and gauge signs while retaining only the original assignment `r`.
These sums form a PVM; their logical observable is exactly `A_hB_h`, and no
forbidden assignment is introduced.  Approximate product ties therefore
bound the difference from `X_x` on a common Gram state, so the original BCS
gap applies with only a fixed incidence constant.

Finally, `M` gauge pairs with one common sign form `E_M`, whose unique
negative-sign simple has dimension `2^M` and group order `2^(1+2M)`.
Its Plancherel mass is `(2^M)^2/2^(1+2M)=1/2`.  Hence duplication neither
weakens the logical gap nor exponentially dilutes the selected spin mass.
