---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-six-exceptions
kind: claim
title: The Hermitian edge trace-norm inequality holds at the rank inequality of the web C_n^4 for every n >= 10 except n = 12, 13, 14, 18, 19, 24
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k4-six-exceptions-windows.md
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/k5_a.log
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/k5_b.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists_k4.log
distinct_from:
  hermitian-edge-trace-norm-web-rank-k4: that uses c_5 >= 7.0857 and leaves twelve n open; this uses c_5 >= 7.168 and leaves six, closing n = 17, 23, 28, 29, 34, 39.
  hermitian-edge-trace-norm-clique-k5-margin: that is c_5 >= 7.0857; the stronger c_5 >= 7.168 is proved inside this claim's route and is used only for the webs.
---

**ESTABLISHED (computer-assisted, exact-rational SDP certificates plus exact rational arithmetic;
unreviewed, not Lean-verified; route `hermitian-edge-trace-norm-web-rank-k4-six-exceptions-windows`).**

**Theorem.** Let `C_n^4` be the web on `Z_n` with `i ~ j` iff the cyclic distance of `i` and `j` is
in `1..4`. For every `n >= 10` except

```text
n  =  12, 13, 14, 18, 19, 24 ,
```

every admissible `C` on `C_n^4` (Hermitian, zero diagonal, zero on non-edges, `|C_ij| >= 1` on
edges) satisfies `||C||_1 >= sqrt3 (n - floor(n/5))`.

The input is `c(K_5) >= 7.168`, i.e. every Hermitian `5 x 5` matrix with zero diagonal and
off-diagonal moduli at least `1` has trace norm at least `7.168`. It is `0.93%` below the numerical
minimum `5 + sqrt5 = 7.2361`, and `3.46%` above the clique bound `4 sqrt3 = 6.9282`.

**Why it matters.** This halves the open list for `k = 4`, from the twelve values of
`hermitian-edge-trace-norm-web-rank-k4` to six. Of the six, `n = 12, 18, 24` need
`c_5 >= 50 sqrt3/12 = 7.2169`, which is `0.27%` below the numerical minimum. Even the true value
`c_5 = 7.2361` leaves `n = 13, 14, 19` open for five-vertex clique windows
(`n eps_5 < sqrt3 (n mod 5)` there, with `eps_5 = 0.308`). Those three need windows with more than
five vertices, for instance `P_7^4` (twelve free phases after gauging).

## Attempts

- 2026-09-18 (w8-078): proved by clique windows and a robust exact-rational SDP branch-and-bound
  for `c(K_5) >= 7.168`, route `hermitian-edge-trace-norm-web-rank-k4-six-exceptions-windows`.
  - Windows `P_7^4` for the six values: they need `c(P_7^4) >= 6 sqrt3 = 10.3923`, against a
    numerical minimum of `10.6872`. With `graphbb_r.py`, a phase box of half-width `0.75` around a
    generic point closes with one solve, but half-width `1.45` does not. That is roughly `4^11`
    cells, many CPU-days. Not run.
