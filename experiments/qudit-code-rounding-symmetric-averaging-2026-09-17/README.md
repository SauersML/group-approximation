# Code-constraint rounding by symmetric averaging: checks (2026-09-17, w3-078)

This directory supports `research/qudit-code-rounding-sharp-factor-all-primes.md`. The proof does
not use it. Every run was single-threaded under `nice -n 10 timeout 1200`, with numpy.

`cc_symmetric_check.py d n trials seed` works for every prime `d`, and uses `D(a,b) = i^(ab) X^a Z^b`
for `d = 2`. It does two things.
- **(a)** It enumerates all nontrivial stabilizer code projectors and checks the operator inequality
  `PQ + QP - PQP - QPQ <= (sqrt r - r)(P + Q)` on every pair whose compression has nonzero spectrum
  `{r}` with `0 < r < 1`. For more than 20000 pairs it checks a random sample of 20000. It also asserts
  that the compression spectrum is constant.
- **(b)** It runs the proof's rounding on random `H = sum_a w_a (I - Pi_a)` with 2 to 7 terms, using
  unit or exponential weights. Each step:
  1. take the top eigenvector in the current code space;
  2. compute `Leak_R`, `M_R` and `L_R` for every nontrivial term;
  3. record `sum_R w_R (Leak_R - M_R L_R/(1+sqrt d))`, which inequality (4) of the proof says is `<= 0`;
  4. post-select on the `R` minimizing `Leak_R/M_R - L_R/(1+sqrt d)` and compress.

  It reports the worst `F(phi)/lambda_min(H)`.

| run | projectors | (a) max eigenvalue | (b) max of (4) | worst ratio | `gamma_d` | log |
|---|---|---|---|---|---|---|
| `2 1 300 1` | 6 | 0 | 3e-17 | 1.707107 | 1.707107 | `sym_d2_n1.log` |
| `2 2 600 4` | 90 | 3e-16 | 4e-16 | 1.707107 | 1.707107 | `sym_d2_n2.log` |
| `3 1 300 2` | 12 | 1e-16 | 2e-15 | 1.577350 | 1.577350 | `sym_d3_n1.log` |
| `3 2 400 5` | 480 (16300 pairs) | 3e-16 | 5e-15 | 1.577350 | 1.577350 | `sym_d3_n2.log` |
| `5 1 200 3` | 30 | 2e-16 | 6e-16 | 1.447214 | 1.447214 | `sym_d5_n1.log` |

There were no violations. The sharp example is reached, and the averaged inequality holds to
rounding error.
