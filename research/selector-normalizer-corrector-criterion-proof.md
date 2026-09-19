---
rg: 2
id: selector-normalizer-corrector-criterion-proof
kind: route
title: Solve the normalizer corrector blockwise along the corrected atom involution
target: selector-normalizer-corrector-has-an-atom-permutation-criterion
requires: []
---

Write the payload and corrector in block-monomial normal form.  The atom
permutation of their product is `tau=alpha sigma`, so involutivity forces
`tau^2=1`, while selected-atom stabilization forces
`alpha(x_0)=x_0`.  Conversely choose inverse block gauges on every
two-cycle of `tau` and a self-adjoint gauge on every fixed point, then absorb
each arbitrary payload block `A_x` into the corrector block
`S_(sigma x)=B_x A_x^*`.  This proves sufficiency without relating distinct
payload blocks.  For the `C_4` countermodel, the only permitted atom
automorphisms are `id` and negation, and composing either with `(0 1 2)`
gives a noninvolution.
