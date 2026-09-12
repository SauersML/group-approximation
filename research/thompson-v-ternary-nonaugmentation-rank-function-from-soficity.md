---
rg: 2
id: thompson-v-ternary-nonaugmentation-rank-function-from-soficity
kind: route
title: A sofic approximation of V read over F_3 gives a detecting Sylvester rank function
target: thompson-v-carries-ternary-nonaugmentation-rank-function
requires: [thompson-v-is-sofic]
artifacts:
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

Artifact Section 4.2.
1. A sofic approximation of `V` gives maps `V -> Sym(n_k)`, which are asymptotically multiplicative and
   asymptotically free.
2. Write the permutations as permutation matrices over `F_3`, and pass to the rank ultraproduct of
   `M_(n_k)(F_3)` with normalized rank. This gives a homomorphism into its units.
3. A permutation moving `m` of `n` points has `rank(P - I) >= m/2`. Freeness therefore gives
   `rk(1 - [g]) >= 1/2` for every `g != 1`.
4. Composing the induced algebra map with the ultraproduct rank gives the required Sylvester matrix rank function
   on `F_3[V]`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 21.1 (valid as a route conditional on thompson-v-is-sofic) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
