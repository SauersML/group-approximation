---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k5-to-k9
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of every web C_n^8 and C_n^9, and of C_n^5, C_n^6, C_n^7 outside 35, 8 and 2 values of n
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k5-to-k9-per-m-lp.md
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-large-k: that proves the same statements for k = 5..9 up to longer exception lists (62, 15, 7, 3 and 1 values for k = 5..9), with one Yudin certificate for all m; this uses a certificate tuned for each m, which empties the lists for k = 8, 9 and shortens those for k = 5, 6, 7.
---

**ESTABLISHED (ordinary proof on top of computer-verified polynomial inequalities, exact rational
arithmetic; unreviewed, not Lean-verified; route
`hermitian-edge-trace-norm-web-rank-k5-to-k9-per-m-lp`).**

Notation is as in `hermitian-edge-trace-norm-web-rank-large-k`. `C_n^k` is the web on `Z_n` with
`i ~ j` iff the cyclic distance of `i` and `j` is in `1..k`, `n >= 2k + 2`. An admissible `C` is
Hermitian, zero on the diagonal and on non-edges, with `|C_ij| >= 1` on edges.

**Theorem.** Every admissible `C` on `C_n^k` satisfies
`||C||_1 >= sqrt3 (n - floor(n/(k+1)))` in each of these cases:

- `k = 8` and `k = 9`: every `n >= 2k + 2`;
- `k = 7`: every `n >= 16` except `n = 22, 23`;
- `k = 6`: every `n >= 14` except `n = 17, 18, 19, 20, 25, 26, 27, 34`;
- `k = 5`: every `n >= 12` except `n = 13-17, 20-23, 26-29, 32-35, 39-41, 45-47, 51-53, 58, 59,
  64, 65, 70, 71, 77, 83, 89` (35 values).

With `hermitian-edge-trace-norm-web-rank-large-k` (every `k >= 10`) and
`hermitian-edge-trace-norm-web-rank-k2`, the rank inequality of every web `C_n^k` with `k >= 8` is
now settled. Among the webs with `k >= 5`, the only open cases are the 45 pairs listed above.

**Why the lists stop where they do.** The clique windows give `||C||_1 >= (n/m) c_m` with
`m = k + 1`. This beats `sqrt3 (n - floor(n/m))` iff `n eps_m >= sqrt3 (n mod m)`, where
`eps_m = c_m - sqrt3 (m-1)`. The certified `eps_m` are `0.0967, 0.2628, 0.4275, 0.6197, 0.8222`
for `m = 6..10`. Local minimisation gives the true values `c_6 = 9.253` (`eps_6 = 0.593`),
`c_7 = 11.124` (`eps_7 = 0.732`) and `c_8 = 13.142` (`eps_8 = 1.018`). With these the clique
windows would close every listed `n`, so the remaining gap is in the lower bound on `c_m`, not in
the covering. The Yudin linear program is flat in the degree (see the experiment README), so the
remaining `n` need a different bound on `c_m` or windows of more than `k + 1` vertices.

## Attempts

- 2026-09-18 (w8-078): proved by per-`m` Yudin certificates, route
  `hermitian-edge-trace-norm-web-rank-k5-to-k9-per-m-lp`. Raising the degree from 6 to 10 or 12
  changes the LP value by less than `0.05` for `m = 6, 7, 8`, so this route cannot reach the
  remaining `n`.
  - The windows `P_{k+2}^k` have 14 (`k = 5`), 20 (`k = 6`) and 27 (`k = 7`) free phases after
    gauging, too many for the phase branch-and-bound of
    `experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/graphbb_r.py`.
