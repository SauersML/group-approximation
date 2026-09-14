---
rg: 2
id: thompson-f-p21-over-f2-degree-seven-exhaustive-proof
kind: route
title: Settle each pair degree by degree with exact F_2 linear algebra on letter-bounded normal forms, and recheck every certificate by composing piecewise-linear maps
target: thompson-f-p21-over-f2-every-pair-meets-in-degree-seven
requires: []
artifacts:
  - research/artifacts/thompson-f-ore-over-f2-2026-09-13.md
---

Notation as in the claim. `F_2[F]` has no zero divisors, since `F` is left-orderable.

**Step 1 (homogeneous splitting).** `a, b` are homogeneous of degree 2 and the relations
`x_j x_i = x_i x_(j+1)` (`i < j`) preserve degree. So `a u = b v` holds componentwise, and the minimal
degree of a nonzero solution is the least `D` for which `A_D : F_2[M_D]^2 -> F_2[M_(D+2)]`,
`(u, v) -> a u + b v`, has a nonzero kernel.

**Step 2 (letter bound).** For `s = x_(s_1) x_(s_2) ∈ S_(2,4)` and `y ∈ M_E`, the normal form of `s y` is
obtained by inserting `s_2`, then `s_1`. Each inserted letter grows by one for every letter it passes, so
the inserted letters are `<= s_2 + E <= E + 2` and `<= s_1 + E + 1 <= E + 2`, and the letters of `y` that
are `> E + 2` are never passed. Write `w ∈ M_D` as `w_low w_high`, where `w_high` collects the letters
`> T`, for `T >= E + 2`. Then `s w = (s w_low) w_high`, and `A_D` is block diagonal over the tails `w_high`,
each block a copy of `A_E` on words with letters `<= T`. Repeating with `T = E + 2`, a nonzero kernel vector
of `A_D` yields one of `A_E` on `F_2[M_(E, E+2)]^2` for some `E <= D`. This is the argument of Step 2 of
`thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof`, with `R(E) = E + 2`.

So the minimal degree equals the least `k` for which `A_k` restricted to `F_2[M_(k, k+3)]^2` has a nonzero
kernel. Since `M_(k,k+2) ⊆ M_(k,k+3)`, a kernel on the larger box at degree `k` gives, by the same step, a
kernel at some degree `<= k` on `M_(E,E+2)`, and conversely.

**Step 3 (computation).** `experiments/thompson-f/ore/ore_linalg.py` (md5 in the artifact), MSI job 737900
and rerun on the login node, iterates `k = 0, 1, 2, ...`. It tests `dim(aV + bV) < 2|V|` for
`V = F_2[M_(k,k+3)]` by incremental Gaussian elimination over `F_2`, for every unsettled pair. Both `aV` and
`bV` have dimension `|V|` by Step 0. All 465 pairs are settled by `k = 7`, with the distribution in the
claim.

**Step 4 (certificates and independent check).**
- `experiments/thompson-f/ore/ore_certify.py` produces explicit nonzero `u, v` of the minimal degree for
  every pair (`s24_certs.json`, md5 in the artifact).
- `experiments/thompson-f/ore/ore_verify.py cert` recomputes `a u` and `b v` for all 465 certificates by
  composing exact piecewise-linear homeomorphisms of `[0,1]` for the standard generators of `F`. It uses no
  normal forms, and it checks `a u = b v ≠ 0`.
- `ore_verify.py nf` checks that the normal-form routine agrees with the PL action on all words of length
  `<= 6` in letters `<= 6` and on random longer words.

The lower bound in item 2 (no solution below the minimal degree) rests on Steps 1–3 only: the rewrite
applies defining relations, and distinct normal forms are distinct elements of `M`.
