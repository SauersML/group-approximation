---
rg: 2
id: mod-s2-monomial-torelli-windings-census
kind: claim
title: On Torelli-abelian representations of Mod(S_2), near-identity separating-twist windings vanish exactly below a monotone congruence limit e_inf of lattice floors; computed exactly on 35 levels up to index 7200 the floor takes only the values 1/5, 1/7 and 1/10
distinct_from:
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that asks for distance from the cube-root scalars; this concerns representations whose separating twist is near the identity and asks whether the trace-log vanishes. Its lattice quantity is a different optimization on the same lattice W, and the two floors behave differently under deepening the level (the cube-root floor stays at 1/15 or 1/30, this one takes the values 1/5, 1/7, 1/10).
  genus-two-mapping-class-group-homology-and-symplectic-quotient: that supplies H_1(Mod(S_2)) = Z/10 and the symplectic quotient; this uses them to compute winding floors on finite-index subgroups.
artifacts:
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings.py
  - experiments/mod-s2-near-identity-windings-2026-09-17/census.py
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings-flag-3_vec-3_pt-5_lag-5_plane-5_pt-7_lag-7_vec-5_line-9_vecpm-4.json
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings-line-4+pt-3_theta-odd+pt-3_frame-2+pt-3.json
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings-line-4_line-6_line-8_line-10_pt-2+pt-7_line-12.json
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings-plane-2+plane-3_pt-2+pt-3.json
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings-plane-5_pt-2+pt-3_theta-even+pt-3_plane-2+lag-3_plane-2+plane-3_flag-2+flag-3_pt-3+pt-5_theta-odd+lag-3.json
  - experiments/mod-s2-near-identity-windings-2026-09-17/windings-sp4_theta-odd_theta-even_pt-2_lag-2_plane-2_flag-2_frame-2_pt-3_lag-3_plane-3.json
---

**ESTABLISHED** through `mod-s2-monomial-torelli-windings-census-proof`. Unreviewed; no novelty claimed.

**Notation.** `M = Mod(S_2)`, `K` its Torelli group, `pi : M -> Gamma = Sp_4(Z)`, `t_s = (a_1 a_2)^6` a
separating twist, and `kappa(U) = (1/2 pi i) Tr log U` (principal logarithm) for a unitary `U` with no
eigenvalue `-1`. A representation `rho` is **Torelli-abelian** if `rho(K)` is abelian.

For `Gamma'` of finite index, `M' = pi^(-1)(Gamma')`, coset representatives `g_c` of `M' \ M`, and
`v_c = [g_c t_s g_c^(-1)] in H_1(M'; Z)`:
- merge cosets with equal `v_c` into classes `j` with multiplicities `mult_j`;
- `W(Gamma') = { w in Z^classes : sum_j w_j v_j = 0 in H_1(M') }`, and `W^* = { h in R^classes : <w, h> in Z
  for all w in W }`;
- the **winding floor** is
  ```text
  e(Gamma') = inf { max_j |h_j| : h in W^*, <mult, h> != 0 } ,      e_inf = inf_(Gamma') e(Gamma') .
  ```

**Statement.**
1. **(MW1) Exact reduction.** Every Torelli-abelian `rho` with `||rho(t_s) - 1||_op < 2 sin(pi e_inf)` has
   `kappa(rho(t_s)) = 0`. Conversely, for each `Gamma'` with `e(Gamma') < 1/2` there is a character `psi` of `M'`
   such that `Ind_(M')^M psi` is Torelli-abelian, `||Ind psi (t_s) - 1|| = 2 sin(pi e(Gamma'))`, and
   `kappa(Ind psi (t_s)) != 0`. So the statement (Z) of `mod-s2-near-identity-torelli-windings-vanish`
   (swarm-0917, not in this worktree), restricted to Torelli-abelian representations, holds **iff**
   `e_inf > 0`, with optimal constant `eta_0 = 2 sin(pi e_inf)`.
2. **(MW2) Monotonicity.** `Gamma'' <= Gamma'` implies `e(Gamma'') <= e(Gamma')`; by the congruence subgroup
   property `e_inf = lim_N e(Gamma(N))` along divisibility.
3. **(MW3) Integrality and certificates.** `<mult, h> in (1/5)Z` for all `h in W^*` (transfer of `t_s`, which
   has order 5 in `H_1(M) = Z/10`). If vectors of `W` of `l1`-norm at most `L` span a rational subspace
   containing `mult`, then `e(Gamma') >= 1/L`.
4. **(MW4) Census.** The exact values below. In particular `e(Gamma(2)) = 1/10`,
   `e(line-6) = e(flag-2 cap flag-3) = 1/7`, and `e_inf <= 1/10`, so the optimal constant for (Z) on
   Torelli-abelian representations is at most `2 sin(pi/10) ~ 0.618`.

## Census table

Level names are those of `census.py` (`pt-p`, `lag-p`, `plane-p`, `flag-p`, `vec-p`: stabilizers of a point,
Lagrangian, plane, flag, vector over `F_p`; `vecpm-4`: vector up to sign mod 4; `line-N`: line in `(Z/N)^4`;
`theta-odd/even`: stabilizers of an odd/even theta characteristic; `frame-2 = Gamma(2)`; `A+B` is the
intersection). Columns: index in `Sp_4(Z)`, `b_1(M')`, number of classes, `rank W`, the order `q` of `mult`
mod `W`, and `e`. Every entry but the last is **exact**: the upper bound is an exact rational `h in W^*` with
`<mult, h> != 0` (Step 1 of the route) and the lower bound is a certificate of Step 4 of the route with
`L = 1/e`; both are in the JSON files, except the last row, where only `1/12 <= e <= 1/10` is proved (the MILP
optimum is `1/10` in floating point, and the greedy search found no certificate at `L = 10`; since a
certificate is only a sufficient condition, this does not show `e < 1/10`). The upper bound `1/10` there also
follows from `Gamma(2)` by (MW2).

| level | index | b_1 | classes | rank W | q | e |
|---|---|---|---|---|---|---|
| sp4 (all of Gamma) | 1 | 0 | 1 | 1 | 5 | 1/5 |
| theta-odd | 6 | 0 | 1 | 1 | 5 | 1/10 |
| theta-even | 10 | 1 | 2 | 1 | 1 | 1/10 |
| pt-2 | 15 | 1 | 2 | 1 | 1 | 1/5 |
| lag-2 | 15 | 1 | 2 | 1 | 1 | 1/5 |
| plane-2 | 20 | 1 | 2 | 1 | 1 | 1/10 |
| pt-3 | 40 | 1 | 2 | 1 | 1 | 1/5 |
| lag-3 | 40 | 1 | 2 | 1 | 1 | 1/5 |
| flag-2 | 45 | 2 | 3 | 1 | 1 | 1/5 |
| vec-3 | 80 | 1 | 2 | 1 | 1 | 1/5 |
| plane-3 | 90 | 1 | 3 | 2 | 1 | 1/5 |
| vecpm-4 | 120 | 2 | 3 | 1 | 1 | 1/10 |
| line-4 | 120 | 2 | 3 | 1 | 1 | 1/10 |
| pt-5 | 156 | 0 | 1 | 1 | 5 | 1/5 |
| lag-5 | 156 | 0 | 1 | 1 | 5 | 1/5 |
| flag-3 | 160 | 2 | 3 | 1 | 1 | 1/5 |
| theta-odd+lag-3 | 240 | 1 | 2 | 1 | 1 | 1/10 |
| theta-odd+pt-3 | 240 | 2 | 3 | 1 | 1 | 1/10 |
| pt-7 | 400 | 0 | 1 | 1 | 1 | 1/5 |
| lag-7 | 400 | 0 | 1 | 1 | 1 | 1/5 |
| theta-even+pt-3 | 400 | 2 | 4 | 2 | 1 | 1/10 |
| line-6 (= pt-2+pt-3) | 600 | 3 | 5 | 2 | 1 | **1/7** |
| vec-5 | 624 | 0 | 1 | 1 | 5 | 1/5 |
| plane-5 | 650 | 0 | 3 | 3 | 1 | 1/5 |
| frame-2 = Gamma(2) | 720 | 9 | 10 | 1 | 1 | 1/10 |
| plane-2+lag-3 | 800 | 2 | 4 | 2 | 1 | 1/10 |
| line-8 | 960 | 2 | 3 | 1 | 1 | 1/10 |
| line-9 | 1080 | 1 | 2 | 1 | 1 | 1/5 |
| plane-2+plane-3 | 1800 | 3 | 10 | 7 | 1 | 1/10 |
| line-10 | 2340 | 1 | 2 | 1 | 1 | 1/5 |
| line-12 | 4800 | 4 | 8 | 4 | 1 | 1/10 |
| line-4+pt-3 | 4800 | 4 | 8 | 4 | 1 | 1/10 |
| pt-2+pt-7 | 6000 | 1 | 2 | 1 | 1 | 1/5 |
| pt-3+pt-5 | 6240 | 1 | 2 | 1 | 1 | 1/5 |
| flag-2+flag-3 | 7200 | 5 | 10 | 5 | 1 | **1/7** |
| frame-2+pt-3 = Gamma(2) cap pt-3 | 28800 | 15 | 30 | 15 | 1 | `[1/12, 1/10]` |

Where a level appears in several JSON files, the exact value is in the file named after the latest run: for
`plane-2+plane-3` this is `windings-plane-2+plane-3_pt-2+pt-3.json` (certificate `L = 10`; an earlier run with the
weaker short-vector search recorded only `1/12`), and for `plane-5` it is the `plane-5_...` file (`L = 5`; the
earlier run recorded `1/6`). `plane-p` is the stabilizer of the symplectic plane `<e_1, f_1>` mod `p`,
`lag-p` that of the Lagrangian `<e_1, e_2>`, `flag-p` that of a line inside a Lagrangian, `vec-p` that of a
vector, and `line-N` that of a primitive vector mod `N` up to units.

Gamma(3) (index 51840) was attempted and was killed for lack of memory (about 8 GB) during the
Reidemeister-Schreier step; it is not in the table.

**The 1/7 witness (line-6).** Five classes, `mult = (24, 288, 192, 72, 24)`, and `W` has basis
`w_1 = (1, 4, 0, -1, 1)` (`l1`-norm 7), `w_2 = (0, 2, 2, 1, 0)` (`l1`-norm 5).
- Upper bound: `h = (1/7, 1/7, -1/14, -1/7, 1/7)` has `<w_1, h> = (1 + 4 + 1 + 1)/7 = 1` and
  `<w_2, h> = (2 - 1 - 1)/7 = 0`, so `h in W^*`, with `max |h_j| = 1/7` and `<mult, h> = 168/7 = 24 != 0`.
- Lower bound: `mult = 24 w_1 + 96 w_2`, so by (MW3) with `L = 7`, `e >= 1/7`.
So `e(line-6) = 1/7` exactly, realized (Step 1 of the route) by a character of the level-6 preimage whose
induced representation has `||rho(t_s) - 1|| = 2 sin(pi/7) ~ 0.868` and `kappa = 24`. The `flag-2+flag-3`
witness (a subgroup of line-6) is in the JSON (five certificate vectors of `l1`-norm at most 7).

## Interpretation and position in the graph

- **(Z) on Torelli-abelian representations is equivalent to one number.** By (MW1)-(MW2) it holds iff
  `e_inf = lim_N e(Gamma(N)) > 0`. This replaces the non-uniform floor `1/(5 [Gamma : Gamma'])` of the w10 attempt
  by an exact lattice invariant, and it covers every Torelli-abelian representation, not only monomial ones
  (Step 2 of the route reduces them to induced characters).
- **The floor is not constant in the level.** Unlike the cube-root distance of
  `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap` (floor `1/15` or `1/30` on every level
  computed), `e` **does** move with the level: `1/5` at `Gamma`, `1/10` at `theta-odd` and `Gamma(2)`,
  `1/7` at levels 6 and `flag-2 cap flag-3`. So the (1/5)-integrality of the winding (MW3) alone does not
  force (Z); only a uniform short-relation bound on `W(Gamma(N))` would.
- **What would decide it.** A sufficient condition for `e_inf > 0` is a uniform `L` such that, for every `N`,
  `mult` lies in the Q-span of `W(Gamma(N))`-vectors of `l1`-norm at most `L` (then `e_inf >= 1/L` by (MW3)).
  In the other direction, a family of levels with `e(Gamma') -> 0` would give Torelli-abelian
  representations with `rho(t_s) -> 1` and `kappa != 0`, i.e. a counterexample to (Z), which by
  `mod-s2-instability-via-vanishing-torelli-windings` is the direction that keeps the gate route
  `deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability` alive. On the 35 levels computed exactly the minimum is
  `1/10`, reached already at index 6, and none of index up to 7200 goes below it (at index 28800 only
  `[1/12, 1/10]` is proved); this is
  evidence (not proof) for `e_inf = 1/10`, i.e. for (Z) on Torelli-abelian representations with
  `eta_0 = 2 sin(pi/10)`.
- **What is not claimed.** Nothing about non-Torelli-abelian representations, and no value of `e_inf`: it is
  only bounded above by `1/10`.
