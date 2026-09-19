---
rg: 2
id: path-map-lamp-mf-proof
kind: route
title: Evaluate representation paths at slow bumps with separated supports
target: path-map-lamp-mf
requires: []
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

## Why sufficient

Enumerate the nonidentity elements `k_1, k_2, ...` of `K`; for each `j`
choose a path `rho^j_s : K -> U(d_j)`, `s in [0,1]`, of genuine
representations with `rho^j_0 = 1` and `rho^j_1(k_j) != 1`; at stage `n`
use the direct sum `rho_{n,s} = (+)_{j <= n} rho^j_s` on `C^{D_n}`.  The
endpoint separations `delta_j = ‖rho^j_1(k_j) - 1‖ > 0` persist for all
`n >= j`.

Uniform continuity of the finitely many functions `s -> rho^j_s(k_i)`,
`i, j <= n`, gives `eta_n > 0` moving all of them by less than `1/n`;
choose a radius `R_n` with `n/R_n < eta_n`.  Choose finite quotients
`q_n : H -> F_n` separating the first `n` elements of `H` and keeping
`q_n(r_i^{-1} r_j)` off `q_n(T)`-words of length `<= 3 R_n` for
`i != j <= n`, exactly as in
`infinite-cyclic-compression-lamp-mf-proof`; let `f_n` be the radius-`R_n`
ramp on `K_n = q_n(L_1) = q_n(L)`.

On `l^2(F_n) tensor C^{D_n}`, represent the root copy of `K` blockwise by
`V_n(k)|_{delta_y tensor -} = rho_{n, f_n(y)}(k)` — an exact
representation for each fixed `y` — and `H` by the right regular
representation on the first factor.  Coset independence: for `h in L_1`
the ramp moves by at most `m(h)/R_n <= eta_n` (large `n`), so conjugation
changes each fixed lamp value by less than `1/n`.  Distinct fixed sites
have disjoint bump supports for large `n` (the `3R_n` separation), and on
the complement of its support a site acts by `rho_{n,0} = 1`; hence
distinct site copies commute exactly for large `n`, and the family is
`H`-equivariant.  All wreath relations hold exactly in the corona.

Faithfulness: a base element with value `a != 1` at site `x_j` evaluates
at the bump center to `rho_{n,1}(a)`, which stays at distance `>= delta`
from `1` once `a`'s dedicated path has entered the direct sum; a
nontrivial `H`-part moves an `l^2(F_n)`-coordinate outright.  Dimension
amplification normalizes coordinates.

**Audit notes (this session).**  Architecture verified: the uniform
continuity/radius coupling, the disjoint-support commutation, blockwise
exactness of the lamp representation, and the two detection estimates.
The path-MAP definition is used only through: (i) exactness of each
`rho_{n,s}`, (ii) `rho_{n,0} = 1`, (iii) endpoint separation.
