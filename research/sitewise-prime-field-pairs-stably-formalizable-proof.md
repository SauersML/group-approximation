---
rg: 2
id: sitewise-prime-field-pairs-stably-formalizable-proof
kind: route
title: Realize the local permutation by a tame automorphism, and use the constant-configuration obstruction for one track
target: sitewise-pairs-over-prime-fields-are-stably-formalizable
requires:
  - tame-maps-induce-every-permutation-of-prime-field-cubes
  - formalizable-pairs-induce-polynomial-automorphisms-on-constants
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Section 4 of the artifact.

1. For `n >= 2`, or `p <= 3`, the first prerequisite realizes `phi` by a formally invertible composite
   `F`. Take `tau*(X_g) = F(X_g)` and `sigma*(X_g) = F^-1(X_g)`.
2. For `n = 1` and `p >= 5`: affine permutations are elementary. Conversely, the constant-configuration
   map of a sitewise pair is `phi`, which the second prerequisite forces to be affine.
3. `phi (+) id` permutes `F_p^(n+1)` with `n + 1 >= 2`, so part 1 applies.
