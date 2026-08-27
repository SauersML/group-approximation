---
rg: 2
id: atlas-a4-context-type-vector-converges-to-regular-point-proof
kind: route
title: Character convergence fixes all A8 and A4 multiplicity proportions
target: atlas-a4-context-type-vector-converges-to-regular-point
requires:
  - atlas-a4-context-network-simultaneous-hs-exactification
  - atlas-a4-context-types-live-in-fixed-rational-polytope
  - a4-triangle-zero-traces-force-regular
---

Let `sigma_n` be the simultaneous exact graph-of-groups representation.  At an
`A8` chart vertex it is `o(1)` in normalized Hilbert--Schmidt norm, on a fixed
generating set, from the canonical regular multiple.  Every element of the
finite group is a fixed word in that generating set, so telescoping gives
`o(1)` closeness on every `g in A8`.  Normalized traces therefore converge to
the regular character: `1` at the identity and `0` elsewhere.

For a finite group, irreducible multiplicities are the character inner
products.  Hence the normalized multiplicity of every `A8` irreducible
converges to its regular proportion `dim(pi)/|A8|`.  This fixes both chart
vertices.

At an `A4` context vertex the exactified order-three generator and order-two
generator are respectively `o(1)` from literal nonidentity elements of the two
regular `A8` charts.  Their normalized traces therefore tend to zero.  Write
the four exact `A4` multiplicities as `m0,m1,m2,m3`.  The same two character
equations used by `a4-triangle-zero-traces-force-regular` give, after dividing
by the common dimension,

```text
m0-m1 -> 0,
m1-m2 -> 0,
m3-3m0 -> 0.
```

Together with the dimension equation this forces the normalized regular
proportions at that context.  There are only thirty contexts, so the conclusion
holds simultaneously.  Thus every normalized vertex type converges to the one
regular point claimed.
