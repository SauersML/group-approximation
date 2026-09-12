---
rg: 2
id: leavitt-cyclic-twist-matrix-structure-proof
kind: route
title: Permutation units, a diagonal twist and Morita equivalence on the Leavitt-visible factor
target: cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra
requires:
  - leavitt-unit-group-algebras-split-over-scalar-characters
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Sections 2 and 3 of the artifact.

- **Permutation units.** `sigma -> sum_i s_(sigma(i)) t_i` is an injective homomorphism
  `S_m -> G`. Each permutation unit fixes `b = sum_i s_i`, and `c b = 1`, which gives the image
  solution.
- **The twist.** `delta g = zeta g delta` follows from `t_i s_j = delta_ij`. On `A_iota` the
  scalar `[zeta]` acts as `zeta`, so `[delta]` permutes the isotypic idempotents of `<g>`, which
  exist because `p` does not divide `m` and `F_q` contains the `m`-th roots of unity. Orthogonal,
  pairwise equivalent idempotents summing to `1` give `M_m(T)`.
- **Cohn form.** `1 <= E_11` in `M_m(T)` becomes `T^m` embedding as a summand of `T` under Morita
  equivalence, which is the Cohn relations.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 9 (scope remark on Theorem 3(5): the onto statement for d >= 3 is unrecorded and not load-bearing) of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
