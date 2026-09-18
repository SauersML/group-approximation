# Clique inequality via energy: scripts and logs (lane w6-078, 2026-09-18)

These files support `research/hermitian-edge-trace-norm-clique-inequality-large-m-proof.md`: the
clique inequality (UCI) `||C||_1 >= sqrt3 (m-1)` for every `m >= 6`, and the obstruction at `m = 4, 5`.
Everything runs single-threaded with numpy/scipy (`OMP_NUM_THREADS=1`).

## The rigorous part

| file | what it does |
|---|---|
| `F_m6_D4.json` | Float coefficients `c_pq` (`0 <= p <= q <= 4`) of the LP polynomial `F`, from `cert_lp.py`, with slack `eta = 0.004`. |
| `verify.py` | **The only computer step the proof depends on.** It rounds the coefficients to multiples of `1e-7`, keeping them as exact `Fraction`s. It then uses interval branch-and-bound over `(r, theta)` in `[0,1] x [0,pi]` to prove `F(z) <= 1/|1-z|` on the closed disc, with outward padding `1e-12` relative plus `1e-14` absolute. Finally it computes `c00` and `F(1)` exactly and checks the quadratic tail `Q(m) >= 0` for all `m >= 6`. Run: `python3 verify.py F_m6_D4.json`. |
| `verify_F_m6_D4.log` | Output: all boxes closed (151,615 boxes, minimum gap `2.2e-8`), the exact rational coefficients, `c00 m^2 - m F(1)` against the target for sample `m`, and the tail check `a > 0`, `Q(6) >= 0.14995`, `Q'(6) >= 0.3878`. |

## Supporting numerics (not used in the proof)

| file | what it does | log |
|---|---|---|
| `cert_lp.py` | Discretised LP that finds `F`. It maximises `c00 m^2 - m F(1)` subject to `F <= (1-eta)/|1-z|` on a polar grid and `c_pq >= 0`. | (writes `F_m6_D4.json`) |
| `yudin.py` | The same LP without slack, for each `m`. Its value is the best degree-4 bound on `E(G)`. | `yudin_D4.log` |
| `energy.py` | BFGS minimisation of `E(G) = sum_{i != j} 1/|1-G_ij|` over `m` unit vectors in `C^k`, with 30 restarts. | `energy_min.log` (`m = 3..8`, `k = m`) |
| `fmatch.py` | Minimises `2 nu_f(1/|1-G_ij|)` over `m` unit vectors in `C^m`. `nu_f` is the largest weight of a fractional perfect matching of `K_m`, taken over all vertices of that polytope. Uses SLSQP with 40 restarts. | `fmatch.log` (`m = 3, 4, 5`) |
| `chain_check.py` | 3000 random admissible `C`, `3 <= m <= 8`. Checks (R1) `|sqrt(d_i d_j) - N_ij| >= |C_ij|` and `||C||_1 >= 2E(G)/(m-1)`. | `chain_check.log` (worst violation `-3.6e-15`, i.e. rounding) |

## Findings recorded in the logs

- The degree-4 LP bound on `E` matches the numerical minimum of `E` at `m = 4` (`7.6569 = 2 + 4 sqrt2`,
  4th roots of unity) and at `m = 5` (`13.7638`, 5th roots of unity). Both are below the needed
  `(sqrt3/2)(m-1)^2`, so uniform averaging cannot prove `m = 4, 5`.
- For `m >= 6` the LP bound exceeds the target, with a ratio that grows with `m` (`1.011` at `m = 6`
  and `1.095` at `m = 20`).
- The fractional-matching form `(M_m)` has numerical minima `1 + sqrt3` (`m = 4`) and `(5 + sqrt5)/2`
  (`m = 5`). These are exactly half the known minima of `||C||_1`, so `(M_4)` and `(M_5)` lose nothing.
