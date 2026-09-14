---
rg: 2
id: thompson-f-p22-over-f2-census-exhaustive-proof
kind: route
title: Settle all pairs of P_(2,2) degree by degree with exact F_2 elimination on letter-bounded normal forms, cross-checked against an independent census and piecewise-linear certificates
target: thompson-f-p22-over-f2-exhaustive-degree-seven-census
requires: []
artifacts:
  - research/artifacts/thompson-f-ore-over-f2-2026-09-13.md
---

Notation as in the claim. `F_2[F]` has no zero divisors, because `F` is left-orderable.

**Step 1 (homogeneous splitting).** `a, b` are homogeneous of degree 2, and the defining relations
`x_j x_i = x_i x_(j+1)` (`i < j`) preserve degree. So `a u = b v` holds degree by degree, and
`δ(a,b)` is the least `D` for which `A_D : F_2[M_D]^2 -> F_2[M_(D+2)]`, `(u, v) -> a u + b v`, has a
nonzero kernel.

**Step 2 (letter bound).** This is Step 2 of `thompson-f-p22-explicit-pair-degree-bound-wiedemann-proof`,
which is field independent. For `s ∈ S_(3,5)` and `y ∈ M_E`, the letters inserted when forming `s y` are
`<= E + 3`, and no letter of `y` above `E + 3` is passed. So `A_D` is block diagonal over the tails of
letters `> T` for any `T >= E + 3`, and a nonzero kernel vector of `A_D` yields a nonzero kernel vector of
`A_E` on `F_2[M_(E, E+3)]^2` for some `E <= D`. Hence `δ(a,b)` is the least `k` for which `A_k` has a nonzero
kernel on `F_2[M_(k, k+3)]^2`.

**Step 3 (computation).** `experiments/thompson-f/ore/ore_linalg.py`, on MSI:
- job 737901 (32 shards) for `k = 0..5` on all pairs;
- job 738304 (64 shards) for `k = 6, 7` on the 109995 pairs unsettled after degree 5.

For `V = F_2[M_(k,k+3)]`, both `aV` and `bV` have dimension `|V|` (no zero divisors), and the program
decides `dim(aV + bV) < 2|V|` by incremental Gaussian elimination with Python integers as bit rows.
The script versions and md5s are recorded in the artifact; the two versions differ only in an added output
field.

**Step 4 (checks).**
- **Normal forms:** `ore_verify.py nf` checks that the rewriting agrees with the faithful piecewise-linear
  action of `F` on `[0,1]` (exact rationals) for all words of length `<= 6` in letters `<= 6` (137256 words)
  and 3000 random longer words, and that distinct normal forms give distinct maps.
- **Independent census:** `experiments/thompson-f/ore_census.py` (commit fd68ee7ab, 2026-09-12) reports
  126144 unsettled pairs at degree 2 and 122745 at degree 3 with letters `<= D+3`. This lane's counts give
  `130305 - 4161 = 126144` and `130305 - 7560 = 122745`.
- **Certificates:** `ore_sample.py` and `ore_verify.py cert` (MSI job 739191) produced explicit `u, v` for a
  deterministic sample of 72 settled pairs: 24 of degree `<= 5`, 24 of degree 6 and 24 of degree 7. They
  recomputed `a u = b v ≠ 0` for all 72 by composing piecewise-linear maps, without normal forms. All checks
  passed.

The lower-bound part of the claim (item 2) rests on Steps 1–3: the rewriting applies defining relations of
`M`, and distinct normal forms are distinct elements.
