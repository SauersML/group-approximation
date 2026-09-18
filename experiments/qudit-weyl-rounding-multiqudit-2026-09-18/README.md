# Qudit Weyl rounding: one-qudit sharp constant and the multi-qudit trace-norm reduction (w5-078, 2026-09-18)

This directory supports these nodes:
- `qudit-weyl-rounding-one-qudit-constant-is-2d-over-sqrt3-pi`
- `qudit-weyl-rounding-constant-is-2d-over-sqrt3-pi`
- `qudit-weyl-rounding-constant-2d-over-sqrt3-pi-via-trace-norm`
- `hermitian-edge-trace-norm-vs-independence`

All scripts are single-threaded Python with numpy and scipy (and cvxpy with SCS for the two SDP
scripts). Run each under `nice -n 10 timeout 1200`.

| script | log | what it checks | result |
|---|---|---|---|
| `check_gram_lemma.py` | `check_gram_lemma.log` | Lemma L (L1) and (L2) on 3000 random Weyl families. The families have `d in {3,5,7}`, `n <= 2`, 2–5 operators with random phases, and both random states and top eigenvectors (the tight regime). The script also computes `c*(d)`. | min of `sum w delta - ||DCD||_1/4` is `+0.00104`; no violation. `c*(d) - 2d/(sqrt3 pi)` is `3.50, 3.52, 3.59, 3.62, 3.77, 3.91, 3.99` for `d = 5, 7, 11, 13, 31, 101, 1009`, and tends to 4 |
| `cmeas.py` | `cmeas.log` | The per-state constant of the line-measurement rounding used in the one-qudit proof, maximized over `psi` by local search from chirped Gaussians | `sup c_meas >= 1.5313` (`d = 5`) and `>= 2.2545` (`d = 7`). The optimizers are three-line states. Proved: `c*(5) = 5.33`, `c*(7) = 6.10` |
| `rho_search.py` | `search_pm2.log`, `search_pm1_big.log` | The semiclassical figure of merit `rho = 4(W - m_iso)/||D Omega D||_1` over random integer antisymmetric `Omega` (any `Omega` is realizable on enough qudits), with weights optimized | `N = 5, 6, 7` with entries in `{-2..2}`: best `2.303, 2.276, 2.228`. `N = 7` with entries in `{-1,0,1}`: `2.3077`. All are `<= 4/sqrt3 = 2.3094`, the one-qudit triangle |
| `kn_relaxed.py` | `kn_relaxed.log` | Complete graphs, purely imaginary `C`: `min ||Omega||_1` subject to `S_jk Omega_jk >= 1` over random tournaments `S` | ratio to `N - 1` is `1.732, 1.886, 1.902, 2.000, 2.039, 2.112` for `N = 3..8`. It exceeds `sqrt3` for `N >= 4` |
| `graph_relaxed.py` | `graph_relaxed.log` | Random graphs, purely imaginary `C`: an SDP in `Q` (`Q + i Omega >= 0` with sign-prescribed edge entries) alternating with an LP in `w` maximizing `sqrt3 (W - alpha_w) - w.q` | min `F/(W - alpha)` is `1.73205 = sqrt3` for `N = 6, 7` and `p = 0.4, 0.6, 0.8`, always at a triangle with weights `1/3` and `q = 2/sqrt3`. The single `1.73186` is solver tolerance |
| `complex_star.py` | `complex_star.log` | (**) with general complex phases and moduli `>= 1`: local minimization of `||DCD||_1/(sqrt3 (W - alpha_w))` over phases, moduli and weights on random graphs (`N = 5, 6`, `p = 0.5, 0.7`) | min ratio `1.000000` at a triangle; never below 1. On `K_3, K_4, K_5` (4 restarts each) it gives `1.000, 1.000, 1.047`; on `K_5` the local search stalls at uniform weights |
| `clique_uniform.py` | `clique_uniform.log` | (**) on `K_m`, uniform weights, complex phases and moduli | `min ||C||_1/(sqrt3 (m-1)) = 1.000, 1.053, 1.045, 1.072, 1.093, 1.093` for `m = 3..8` |

What the computations rule out. Within the semiclassical class (all `delta_j` small, `C` nearly
imaginary), no configuration of up to 7 Weyl directions on any number of qudits beats the
one-qudit triangle. So an `n`-qudit refutation of `c_d = 2d/(sqrt3 pi) + O(1)` would need at least
8 directions, or states far from the semiclassical regime. The searches are local, so they are
evidence, not certificates.
