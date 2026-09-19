---
rg: 2
id: sl2-half-deligne-monomial-third-floor-calibration
kind: claim
title: In the Deligne triple cover of SL_2(Z[1/2]), where b_2^(2) > 0 and property T fails, the monomial third floor equals the Kahler value exactly on every small congruence set, beyond every single-cycle bound
distinct_from:
  deligne-schreier-complexes-have-a-uniform-third-cellular-floor: that is the Sp_4(Z) floor, where MILP gave only upper bounds; this is the same invariant for SL_2(Z[1/2]), a calibration world with b_2^(2) > 0 and no property T, where the MILP closes exactly.
  deligne-third-floor-has-no-character-certificate: that computes the Sp_4(F_2) census and proves no character certificate exists; this reproduces the exact-floor-beats-single-cycle phenomenon in SL_2(Z[1/2]), so that phenomenon is not a signature of higher-rank rigidity.
  sl2-half-rational-h2-refutes-torsion-normalized-op-basin: that uses H^2(PSL_2(Z[1/2]), Q) = Q to refute a normalized basin; this measures the operator-norm monomial floor of the Deligne class itself.
  sl2-half-central-extension-not-residually-amenable: that proves the Deligne cover is not residually amenable; this asks whether its monomial third floor is uniform over finite Schreier complexes.
artifacts:
  - experiments/deligne-sl2-calibration-2026-09-17/lifts.py
  - experiments/deligne-sl2-calibration-2026-09-17/sl2_milp.py
  - experiments/deligne-sl2-calibration-2026-09-17/cycles.py
  - experiments/deligne-sl2-calibration-2026-09-17/feas.py
  - experiments/deligne-sl2-calibration-2026-09-17/results.log
---

**OPEN (numerical calibration).** Notation of `deligne-schreier-complexes-have-a-uniform-third-cellular-floor`,
transplanted from `Sp_4(Z)` to `G = SL_2(Z[1/2])`. The claim asks whether there is `c > 0` with

```text
mu_(1/3)(X) = dist_inf( kappa/3 , delta C^1(Y_X; R) + C^2(Y_X; Z) ) >= c     for every finite G-set X,
```

equivalently `||f_R||_cell >= 3c` for every `f in kappa + 3 H^2(Y_X; Z)`. What is proved is below; the uniform
claim is open.

**Why this world calibrates the Sp_4 lane.**
- `W_3 = G~ / <z^3>`, with `G~` the preimage of `G` in the universal cover of `SL_2(R)`, is the analogue of `E_3`.
  Deligne-Raghunathan non-residual-finiteness is recorded for a closely related finite central extension in
  `sl2-half-central-extension-not-residually-amenable`; that it is literally `W_3` is not checked here. What is
  checked: on every set in the cycle column below there is an integral 2-cycle `c` with `kappa(c) = 1 mod 3`, so
  `mu(X) > 0` there.
- But `G` has `b_2^(2) > 0` and `H^2(G, Q) = Q`, it is not matricially stable
  (`sl2-half-rational-h2-refutes-torsion-normalized-op-basin`), and it has no property T. Its vertex groups
  `SL_2(Z)` have congruence subgroups with huge `H^1`, so the cusp freedom that property T removes in `Sp_4(Z)` is
  present here.
- Hence any phenomenon seen in both worlds at small levels is not evidence for a rigidity mechanism specific to
  `Sp_4`.

**Presentation and lift exponents** (`lifts.py`, every relator checked exactly in the universal cover,
`z` the generator of `pi_1(SL_2(R))`). `G = SL_2(Z) *_{Gamma^0(2)} a SL_2(Z) a^{-1}` (Serre, Trees II.1.4),
`a = diag(sqrt2, 1/sqrt2)`, generators `x = S~`, `y = (ST)~` (with `y^3 = x^2`) and `X, Y` their conjugates by `a`:

| relator | word | lift `r~ = z^k` |
|---|---|---|
| x4 | `x^4` | 1 |
| xy | `x^2 y^-3` | 0 |
| XY | `X^2 Y^-3` | 0 |
| xX | `x^2 X^-2` | 0 |
| T | `x^-1 y x^-1 y Y^-1 X` | 0 |
| U | `x^-1 y^-1 x x Y X^-1 Y X^-1` | 0 |

`kappa` is the cellular 2-cochain `r -> k(r)` on the Schreier 2-complex `Y_X`; `b_2(Y_X) = 3|X| - 1 + b_1` and
`b_1 = 0` on every finite-index subgroup (congruence subgroup property for `SL_2(Z[1/2])`).

**Computation** (`sl2_milp.py`, HiGHS, exact MILP for `mu_(1/3)` with a spanning-tree gauge; `results.log`).
`P1_N` = `G` acting on `P^1(Z/N)`, `V_N` = primitive vectors of `(Z/N)^2`, `PV_N` = primitive vectors mod `+-1`,
`SL_N` = `SL_2(Z/N)` by left multiplication (all through `Z[1/2] -> Z/N`, `N` odd). These are orbit sets, all
transitive.

| set | points | `mu_(1/3)` | dual bound | secs | min detecting cycle | single-cycle bound |
|---|---|---|---|---|---|---|
| point | 1 | 1/51 | 1/51 | 1.2 | 17 | 1/51 |
| P1_3 | 4 | 1/51 | 1/51 | 5.7 | 17 | 1/51 |
| PV_3 | 4 | 1/51 | 1/51 | 5.6 | 17 | 1/51 |
| P1_5 | 6 | 1/51 | 1/51 | 22 | 18 | 1/54 |
| P1_7 | 8 | 1/51 | 1/51 | 39 | 20 | 1/60 |
| V_3 | 8 | 1/51 | 1/51 | 34 | 18 | 1/54 |
| P1_9 | 12 | 1/51 | 1/51 | 504 | 18 | 1/54 |
| PV_5 | 12 | 1/51 | 1/51 | 363 | 18 | 1/54 |
| P1_13 | 14 | 1/51 | 1/51 | 78 | 22 | 1/66 |
| P1_11 | 12 | in (0.0195, 1/51] | 0 (1200 s); cap 0.0195 infeasible | 716 | 18 | 1/54 |
| V_5 | 24 | <= 1/51 | 0 (1200 s) | - | 21 | 1/63 |
| P1_17 | 18 | <= 1/51 | - | - | 22 | 1/66 |
| P1_19 | 20 | <= 1/51 | - | - | 18 | 1/54 |
| SL_3 | 24 | <= 1/51 | cap 0.0195: no verdict (3200 s) | - | 22 | 1/66 |
| P1_15 | 24 | <= 1/51 | - | - | 29 | 1/87 |
| PV_7 | 24 | <= 1/51 | - | - | 35 (`kappa = -2`) | 1/105 |
| P1_25 | 30 | <= 1/51 | - | - | 35 | 1/105 |

"Min detecting cycle" is the least `l1` norm of an integral 2-cycle `c` with `kappa(c) = 1 mod 3`, solved to
optimality (`cycles.py`, dual bound above norm - 1 in every row). The single-cycle bound is `dist(kappa(c)/3, Z)/||c||_1`.
Feasibility checks at cap `0.0195 < 1/51` (`feas.py`) are in `results.log`: `P1_7` is infeasible in 38 s,
`P1_11` in 716 s (so `mu(P1_11) > 0.0195 > 1/54`, again above its single-cycle bound), `SL_3` gives no verdict in 3200 s.

**What is proved (by hand, all X transitive).**
1. `||kappa_R||_cell = 1/17` on every `Y_X`, where `||kappa_R|| = min_beta sup |kappa - delta beta|`. Upper bound: an
   optimal real `beta` on the one-point complex pulls back to every `X`. Lower bound: averaging an optimal `beta` on `X`
   over the fibres of `X -> point` gives a real `beta'` on the point with no larger sup, and on the point the integral
   2-cycle `c0 = x4 + 4 xy + 8 T + 4 U` has `kappa(c0) = 1` and `||c0||_1 = 17`, so the sup is at least `1/17`. Equality on
   the point is LP duality: the real point cycles are `((a+b)/12, (2a-b)/3, (2b-a)/3, (a-2b)/6, a, b)` on
   `(x4, xy, XY, xX, T, U)`, and with `a + b = 12` the norm is
   `1 + |a-4| + |8-a| + |a-8|/2 + |a| + |12-a| >= 17`, with equality at `a = 8`, which is `c0`.
2. Hence `mu_(1/3)(X) <= 1/51` for every `X` (take the zero integral part), and `mu_(1/3)(point) = 1/51` exactly
   (`c0` gives `dist(1/3, Z)/17`).
3. For every integral 2-cycle `c` on `Y_X`, `mu_(1/3)(X) >= dist(kappa(c)/3, Z)/||c||_1` (pair the defect with `c`).
   The table's last column is the best such single-cycle bound; for `P1_5, V_3, P1_7, P1_9, PV_5, P1_13` it is strictly
   below the exact value `1/51`.

**Heuristic, not proved.** A detecting cycle cannot be local once `X` is large: near a cusp of `P1_p` the complex looks
like the Schreier complex of `G/B(Z[1/2])`, where the central extension splits on `B`, and near an elliptic point like
`G/C_4`; on both infinite quotients `kappa` takes values in `3Z` on cycles. So minimal detecting cycles must grow with
the level (the table shows growth from 17 to 35 by 30 points), and single-cycle bounds go to 0. Whether the exact
floor stays at `1/51` is exactly the open question, now in a world without property T.

**What this calibrates.** In `Sp_4(Z)` (`deligne-third-floor-has-no-character-certificate`) the small-level census
gives the Kahler value, and the exact floor beats single-cycle bounds. Both phenomena recur here, with a larger gap
(1/51 vs 1/66 at 14 points), in `SL_2(Z[1/2])`: `b_2^(2) > 0`, no property T, not matricially stable. So neither
phenomenon is evidence that `Sp_4` rigidity drives the uniform floor. The MILP closes here up to 14 points (6
relators) but not at `Sp_4` scale (14 relators), and neither lane reaches the large levels where a decay would show.

## Attempts

- 2026-09-19, swarm-0917-w16-w16-deligne-break (belief breaker, calibration). Built the `SL_2(Z[1/2])` presentation
  with exact lifts, the exact MILP, the detecting-cycle ILP and the sub-Kahler feasibility check. Result: exact
  `mu = 1/51` on 9 sets up to 14 points; minimal detecting cycles 17 to 35 up to 30 points; exact beats single-cycle
  from 6 points on. No counterexample and no decay. The optimization MILP's dual bound stays 0 from 12 points (`P1_11`, `V_5`);
  the feasibility form still certifies `mu(P1_11) > 0.0195` but gives no verdict on `SL_3` (24 points). Status OPEN. Dead end for this tool: exact MILP beyond about 14 points. Next: a dual certificate family
  (averaged over cusps) or a structured primal with defect below 1/51 on `P1_p`, p large.
