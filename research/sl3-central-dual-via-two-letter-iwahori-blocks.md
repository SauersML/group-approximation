---
rg: 2
id: sl3-central-dual-via-two-letter-iwahori-blocks
kind: route
title: Kill the central separator using the two conjugate-letter block systems over the Iwahori overlap
target: sl3-hnn-central-dual-gap-vanishes
requires:
  - full-hnn-regularity-is-a-quasiregular-unitary-orbit
  - letter-central-matrix-range-separation-is-morita-neutral
---

**INVALIDATED PROPOSAL.**  Put `U=phi(h)Tphi(h)^*` and decompose the matrix
space simultaneously by the spectral multiplicity systems of `T` and `U`.
Because both letters centralize

```text
C=Lambda cap hLambda h^(-1),
```

use the Iwahori overlap actor and the canonical mixed moments of the two
letters to couple the blockwise Choi cones.  Apply a two-letter
support-function inequality to eliminate the original `T`-central
separator.

`two-conjugate-letter-overlap-data-is-morita-neutral` gives exact finite
countermodels to precisely these inputs.  Finite regular quotients of
`C_k*Z` realize arbitrarily large canonical windows of the conjugate pair,
and an arbitrary overlap representation and matrix-range separator tensor
through their common multiplicity factor with unchanged gap.

The missing input is not another principal-angle or joint spectral-block
estimate.  A replacement must use that `phi(h)` transports the full first
lattice vertex to the second one, including generators outside `C`; this is
the endpoint-compatibility/local-global content absent from the tensor
countermodel.

