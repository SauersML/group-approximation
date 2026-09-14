---
rg: 2
id: schreier-family-amplification-proof
kind: route
title: Cut partial actions from Følner sets of the coset spaces, and amplify the positive-density separation by products
target: separating-repetitive-amenable-schreier-families-force-soficity
requires: []
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

Section 3 of the artifact.

- **Partial action.** Fix a finite `E` and put `F = E cup E E cup {1}`. On a Følner set `Φ` of
  `H_F\G`, let `phi(g)` extend the partial injection `v |-> v.g^-1` to a permutation of `Φ`.
- **Defect.** For `g, h` in `E`, `phi(g) phi(h) = phi(gh)` off `∂_2 Φ`, since `(v.h^-1).g^-1 = v.(gh)^-1`.
- **Separation.** At a vertex whose labelled 1-ball matches the base, `g` in `E \ {1}` moves the
  vertex, because `g^-1` lies in `F F^-1 \ {1}` and hence not in `H_F`. Such vertices have density at
  least `delta > 0`.
- **Amplification.** The diagonal action on `Φ^r` has fixed-point fraction at most `(1 - delta/2)^r`
  and defect at most `r` times the boundary fraction. Choose `r`, then `Φ`.
- **Reach.** A normal separating `H` makes `G -> G/H` injective and multiplicative on `F`, which is a
  local embedding into `G/H`.
