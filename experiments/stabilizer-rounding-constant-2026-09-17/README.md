# Stabilizer rounding constant: computations (2026-09-17, sw-078)

Supports `research/stabilizer-rounding-constant-is-one-over-sqrt2-proof.md`. The proof does
not use these computations. All runs: `nice -n 10 timeout 1200`, single-threaded.

| script | what it does | result |
|---|---|---|
| `search_sr_constant.py n restarts seed` | enumerates stabilizer states (6, 60, 1080 for n=1,2,3); maximizes `(lambda_max - stab)/(W - lambda_max)` over signed Pauli weights on random supports (Nelder--Mead) | n=1: 0.7071067812; n=2 (300 restarts): 0.7071067812; n=3 (400 restarts, stopped after restart 1): 0.707107 |
| `magic_candidates.py` | the same ratio for `K = sum_P sign(x_P)|x_P|^p P`, `x` the Pauli vector of T^n, CS, CCZ, W and random states, n<=3 | max 0.707107 (T state) |
| `dual_lp.py n restarts steps seed` | minimax dual: `c(psi) = min c` such that a stabilizer mixture `m` has `|m_P - (1+c)x_P| <= c` for all `P`; the optimal constant is `sup_psi c(psi)`. LP via HiGHS, local search over `psi` | n=1: 0.7071068; n=2: 0.7071068; n=3 (stopped after restart 4): 0.7071062 |
| `dual_special.py` | dual LP at special states | TT, TF, TTT, CS x T: 1/sqrt2; FF, FFF, F x 0: 1/sqrt3; CS, CCZ, W: 1/2; CT: 0.3895; a Hoggar-type vector: 1/3 |
| `greedy_postselect_check.py trials seed` | runs the proof's rounding (post-select on the term of largest expectation, recurse) on random Pauli sums with n<=4 and checks `stab >= (1+1/sqrt2)lambda - W/sqrt2` | 3000 trials (seed 7), no violation, min normalized slack -2.1e-15 |

Dual formulation (proved by LP minimax, since (SR*) is increasing in `lambda`):
(SR*) holds for all `K` iff every pure state lies in `(SP_n + c B_inf)/(1+c)`, where
`SP_n` is the stabilizer polytope and `B_inf` the unit cube in Pauli coordinates.
