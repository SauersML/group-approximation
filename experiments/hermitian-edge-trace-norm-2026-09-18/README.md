# Hermitian edge trace-norm inequality: odd cycles, facets, cliques (lane w6-078, 2026-09-18)

Supports `hermitian-edge-trace-norm-k4-free-h-perfect`, `hermitian-edge-trace-norm-clique-inequality`,
`hermitian-edge-trace-norm-other-stab-facets` and the route `hermitian-edge-trace-norm-via-stab-facets`.
Everything runs single-threaded (`OMP_NUM_THREADS=1`) in seconds to a few minutes with numpy/scipy.

| script | what it checks | log |
|---|---|---|
| `cycle_check.py` | Theorem A: for odd `n = 3..13`, flux scan at unit moduli, 20000 random admissible `C`, and L-BFGS-B over moduli and phases all give `min ||C||_1 = 2 cot(pi/(2n))`, never less | `cycle_check.log` |
| `facet_min.py` | local minima of `||D_a C D_a||_1 / (sqrt3 (a(V) - alpha_a))` at facets that are neither cliques nor odd holes (antiholes, wheels with lifted hub, webs), plus `C_5, C_7`; all ratios `>= 1.108` | `facet_min.log` |
| `clique_min.py m seed restarts` | minimum of `||C||_1` over Hermitian `C` with zero diagonal and off-diagonal moduli `>= 1` on `K_m` (moduli `1 + s^2`, phases free; exact gradient from the sign matrix) | `clique_min_small.log` (`m = 3..6`), `clique_min_large.log` (`m = 7, 8, 10`) |
| `clique_struct.py m` | prints the spectrum, `diag|C|/2` and the gauge in which the rank-1 part is real, at the clique optimum | (interactive) |

Findings.
- Odd cycles: exact minimum `2 cot(pi/(2n))` (6.155, 8.763, 11.343, 13.910, 16.471 for `n = 5..13`),
  far above the needed `sqrt3 (n+1)/2`.
- Cliques are the tight family. The minima over `K_m`: `2 sqrt3` (m=3, ratio 1), `2 + 2 sqrt3` (m=4, 1.052),
  `5 + sqrt5` (m=5, 1.044), then 9.254, 11.129, 13.208, 17.108 for `m = 6, 7, 8, 10`. Every optimum
  has unit moduli and one eigenvalue of one sign (so `||C||_1 = 2 ||C||_op`).
- No counterexample to (**) was found.
