---
rg: 2
id: sl3-depth-two-clifford-fiber-has-thirty-six-types
kind: claim
title: The deepest dyadic SL3 Clifford fiber has exactly thirty-six coadjoint types
artifacts:
  - experiments/sl3_mod4_adjoint_orbits.py
  - experiments/sl3_mod4_adjoint_orbits.json
distinct_from:
  depth-two-clifford-types-form-a-finite-fiber-folner-graph: that proves only that the level-independent fiber is finite; this exhaustively computes its orbit count and orbit-size distribution.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that computes branching data for selected permutation modules at level eight; this classifies every character orbit of the universal deepest-two-layer kernel.
---

Under the trace-pairing identification

```text
ker(SL_3(Z/2^a)->SL_3(Z/2^(a-2)))^hat
 ~= sl_3(Z/4Z),                                        (CT36-1)
```

the conjugation action factors through `SL_3(Z/4Z)`.  It has exactly `36`
orbits.  Their sizes, with multiplicities, are

```text
1^1, 21^1, 24^1, 28^1, 42^1, 56^1, 84^1,
336^2, 448^2, 672^3, 896^1, 1344^4,
1536^4, 2688^5, 3584^4, 5376^4.                        (CT36-2)
```

The weighted sum is `65536=4^8`, the order of the additive module
`sl_3(Z/4Z)`.  Thus a bounded-depth local compatibility test for the
dyadic branch has only thirty-six vertex types before stabilizer-projective
and multiplicity data are added.

