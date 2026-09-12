---
rg: 2
id: range-projection-far-from-translation-observables-proof
kind: route
title: Match an excluded configuration with an image configuration of the same stabilizer and translate both far away
target: range-projection-far-from-translation-observables
requires: []
artifacts:
  - research/artifacts/simple-kazhdan-hosts-2026-09-12.md
---

Section 3.4 of the artifact gives the complete proof. The argument is due to
`gk-observables`; the landing lane re-derived each step.

- Fill the missing cylinder into the background `c` to get an excluded
  configuration `u`, with finite stabilizer `K`.
- Fill a right coset `Kt` of the background `b` to get `x` with `Stab(x) = K`,
  and put `y = tau(x)`.
- Translate `u` and `y` so that their supports avoid `F ∪ S^-1 F` for a finite
  combination `O = sum_g a_g pi_c(g)` with every `a_g` local on `F`.
- Then `<h.u|O|h.u> = <h.y|O|h.y>`, while `P` takes the values `0` and `1` on
  these vectors.

Under property (T) the Kazhdan projection is the projection onto invariant
vectors, and the only finite orbit is `{c}`.
