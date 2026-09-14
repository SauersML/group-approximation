---
rg: 2
id: strict-kazhdan-compression-no-deficit-proof
kind: route
title: The Kun--Thom actor is residually finite, hence sofic, hence Rokhlin-maximal
target: strict-kazhdan-compression-gives-no-bernoulli-deficit
requires: [kun-thom-actor-is-rf-but-neither-rfd-nor-llp, sofic-radical-localizes-bernoulli-deficit-witnesses]
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Section 7.4 of the artifact.

1. **Sofic.** The first prerequisite makes `G` residually finite. The actions of `G` on its finite
   quotients are exact permutation models that separate any finite set of elements, so `G` is sofic.
2. **Maximal.** A sofic group has trivial sofic radical. By the second prerequisite no configuration
   over `G` has `Phi < log q`, so `G` is Rokhlin-maximal at every `q`.
3. **No compression.** By Proposition 1 of the artifact, a measurable alphabet compression over `G`
   would give a generating partition with fewer pieces, hence a deficit.
4. **Patterns.** `Phi` depends only on the incidence pattern of the points, so a configuration over `U`
   whose pattern is realized injectively in `G` also has `Phi >= log q`.
