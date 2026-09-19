---
rg: 2
id: mod-s2-short-generated-torelli-relations-pin-one-thirtieth-proof
kind: route
title: The transfer of 5 t_s is a positive relation 5 1_X; short generators force every near-1/3 lift to agree with the constant 3/10 on W, and positivity of the difference contradicts 5 1_X
target: mod-s2-short-generated-torelli-relations-pin-one-thirtieth
requires:
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
  - mod-s2-induced-torelli-characters-have-positive-relation-floors
artifacts:
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact_d.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-phi.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-phi.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/run-check-phi.log
  - experiments/mod-s2-three-sylow-census-2026-09-17/level4_sg.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-gamma4.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-gamma4.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/run-level4.log
  - experiments/mod-s2-three-sylow-census-2026-09-17/level8_sg.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-level8-all-fast.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/run-level8-all-fast.log
---

Notation as in the target.

**Inputs.**
- **[TA]** `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`. It supplies the definitions of
  `X`, `v_c`, `W(Gamma')` and `d(Gamma')` (the minimum over `theta in (R/Z)^X` with `sum_c w_c theta_c = 0`
  for all `w in W(Gamma')`, which is attained). It also supplies, verbatim:
  - (TA2): "If `Gamma'' <= Gamma'`, then `d(Gamma'') <= d(Gamma')`. Every finite-index subgroup contains
    some `Gamma(N)`. Hence `d_inf = inf_N d(Gamma(N))`";
  - the (TA4) rows "| `Sp_4(Z)` | 1 | 0 | 1 | 1 | 5 | 1/15 |" and
    "| `Gamma(2)` | 720 | 9 | 10 | 1 | 10 | 1/30 |", with columns index, `b_1(M')`, classes, `rank W`,
    cert `||w||_1`, `d`, where "classes" is the number of distinct `v_c`.
- **[RF]** `mod-s2-induced-torelli-characters-have-positive-relation-floors`, (PR), verbatim: "`B` contains
  the nonzero vector `b_tr = 5 c >= 0` of mass `5 [Sp_4(Z) : Gamma']` ... So no real character of
  `Lambda` is positive on all separating twists (Gordan's alternative)". Step 1 gives a direct proof of the
  form used here.
- **Transfer** (standard; Brown, *Cohomology of groups*, III.9). For right cosets `M' g_c` the transfer
  `tr : H_1(M) -> H_1(M')` is `tr[g] = sum_c [g_c g g_(c.g)^(-1)]`, where `g_(c.g)` represents `M' g_c g`.

## Step 1. The positive relation `5 1_X` lies in `W(Gamma')`

1. The [TA] row for `Sp_4(Z)` has one class, so `X` has one element, and it has a certificate `w in W(Sp_4(Z))`
   with `||w||_1 = 5`. So `w = +-5`, and `5 [t_s] = 0` in `H_1(M)`.
2. `g_c t_s = (g_c t_s g_c^(-1)) g_c`, and `g_c t_s g_c^(-1)` lies in `K <= M'`. So `M' g_c t_s = M' g_c`, and the
   transfer formula gives `tr[t_s] = sum_c v_c`.
3. Hence `5 sum_c v_c = tr(5 [t_s]) = 0`, that is, `5 1_X in W(Gamma')`. This is (PR) of [RF], written in the
   coordinates `X`.

## Step 2. Upper bound `d(Gamma') <= 1/30`

Under (SG*), every generator `w in S` has `aug(w) in 10Z`, so `aug(W) <= 10Z`. Put `theta = (3/10) 1_X`. For
`w in W`, `sum_c w_c theta_c = 3 aug(w)/10 in Z`, so `theta in W^perp`, and `|| 3/10 - 1/3 || = 1/30`.

## Step 3. Lower bound `d(Gamma') >= 1/30`

1. Suppose `theta in W^perp` has `max_c ||theta_c - 1/3|| < 1/30`. Choose real lifts `h_c` of `theta_c` with
   `|h_c - 1/3| < 1/30`. For every `w in W`, `n_w = sum_c w_c h_c` is an integer, because
   `sum_c w_c theta_c = 0` in `R/Z`.
2. For `w in S`, `w != 0`:
   `|n_w - aug(w)/3| = |sum_c w_c (h_c - 1/3)| <= ||w||_1 max_c |h_c - 1/3| < ||w||_1 / 30`.
   By (SG*), `n_w = 3 aug(w)/10`. (For `w = 0` this holds trivially.)
3. Put `x = h - (3/10) 1_X in R^X`. Then `sum_c w_c x_c = n_w - 3 aug(w)/10 = 0` for `w in S`. By linearity
   this holds for all `w in W`, since `S` generates `W`.
4. For every `c`, `x_c = h_c - 3/10 > (1/3 - 1/30) - 3/10 = 0`.
5. Applying Step 3.3 to `w = 5 1_X` (Step 1) gives `5 sum_c x_c = 0`. But Step 3.4 gives `5 sum_c x_c > 0`.
   This is a contradiction.

So every `theta in W^perp` has `max_c ||theta_c - 1/3|| >= 1/30`. With Step 2, `d(Gamma') = 1/30`. This is
(SG-pin).

**(SG) implies (SG*).** Take `aug(w) = 0` and `||w||_1 <= 30`: the only integer in `(-1, 1)` is `0`. Take
`aug(w) = 10` and `||w||_1 <= 20`: the integers within distance less than `2/3` of `10/3` are only `3`. The
case `aug(w) = -10` is symmetric.

## Step 4. Class coordinates, and the checks (item 3)

1. *Class coordinates suffice.* Let `Cl` be the set of distinct classes and `p : Z^X -> Z^Cl` the map that sums
   over fibres. Since `sum_c w_c v_c` depends only on `p(w)`, `W = p^(-1)(W_Cl)`, where `W_Cl` is the
   relation lattice of the distinct classes.
   - `ker p` is generated by the `e_c - e_c'` with `v_c = v_c'`. These have `aug = 0` and `l1 = 2`.
   - Fix one coset `c(v)` for each class `v`, and let `s : Z^Cl -> Z^X` be the lift `e_v -> e_(c(v))`. It
     preserves `aug` and `l1`.
   - So if a generating set of `W_Cl` satisfies (SG) or (SG*), then its image under `s`, together with the
     `e_c - e_c'`, is a generating set of `W` with the same property.

   `exact_d.py` works in class coordinates (its matrices have one column per class).
2. *`Gamma(2)`.* `Gamma(2)` is normal in `Sp_4(Z)`, so `M' = pi^(-1)(Gamma(2))` is normal in `M`.
   - For `g in M`, conjugation by `g` induces an automorphism of `H_1(M')` that sends `v_c` to `v_(c')`,
     where `M' g_(c') = g M' g_c`.
   - Left multiplication is transitive on `M' \ M`, so these automorphisms permute the classes
     transitively. Every class therefore occurs for `720/10 = 72` cosets.
   - By Step 1, `p(5 1_X) = 360 (1, ..., 1)` lies in `W_Cl`.
   - The [TA] row gives `rank W_Cl = 1`, so `W_Cl` lies in the line through `(1, ..., 1)`, and every
     element of `W_Cl` is `k (1, ..., 1)` with `k` an integer.
   - The certificate has `||w||_1 = 10`, so it is `+-(1, ..., 1)`. Hence `W_Cl = Z (1, ..., 1)`, and its
     generator has `|aug| = l1 = 10`. So (SG) holds.
3. *`Sp_4(Z)`.* `W = 5Z` has `aug = 5`, which is not in `10Z`, so (SG*) fails. This is consistent with
   `d = 1/15`.
4. *Computed levels.* `exact_d.py --check w-<V>.json` does three things:
   - it LLL-reduces the saved HNF basis of `W_Cl`;
   - it checks exactly that the reduced basis spans the same lattice (equal HNF);
   - it records `short_generated` (SG) and `short_generated_general` (SG*), with the row types
     `(|aug|, l1)`.

   The results are in `exact-<V>.json`. For `V = U, max_0, max_1, max_2` both flags are `true`. The
   largest row types are:

   | `V` | largest `(0, l)` | largest `(10, l)` |
   |---|---|---|
   | `U` | `(0, 12)` | `(10, 12)` |
   | `max_0` | `(0, 14)` | `(10, 18)` |
   | `max_1` | `(0, 16)` | `(10, 18)` |
   | `max_2` | `(0, 12)` | `(10, 12)` |
   | `Gamma(4)` | `(0, 18)` | `(10, 18)` |
   | `Phi` (plain basis; fails) | `(0, 24)` | `(10, 22)` |
   | `Phi` (split, item 5) | `(0, 24)` | `(10, 16)` |

5. *(SG0) implies (SG).* Assume (SG-a) and (SG-b). For `w in W`, `aug(w) = 10k` with `k` an integer, and
   `w - k w_1 in W_0`. So `W = W_0 + Z w_1`. A generating set of `W_0` with `l1 <= 30` (these vectors have
   `aug = 0`), together with `w_1` (`aug = 10`, `l1 <= 20`), satisfies (SG).
   - `exact_d.sg_split` tests this: it takes `w_1` among the short rows of `|aug| = 10` (and the positive
     relation found by the MILP, when its mass is 10), and forms `R_i - (aug(R_i)/10) w_1` from the basis rows.
   - It then LLL-reduces the result, and checks exactly that `HNF(W_0 basis + w_1) = HNF(W)`.
6. *`Gamma(4)` and the index-two groups `G_chi`.*
   - `level4_sg.py` builds `Gamma(4)` in the Pbar model (512 cosets). (SG) holds on the LLL basis
     (`run-level4.log`). `sg_split` gives `w_1 >= 0`, `||w_1||_1 = 10`, and `W_0` max `l1` 18.
   - `level8_sg.py` builds the fifteen `G_chi`, `Gamma(8) < G_chi < Gamma(4)`, one per `Sp_4(F_2)`-orbit
     of `chi` (1024 cosets each; the orbit sizes sum to 1023, so every `chi` is covered up to
     conjugacy, and conjugate groups have the same `W` up to permuting classes).
   - At every orbit `sg_split` passes with `w_1 >= 0`, `||w_1||_1 = 10`, and `W_0` max `l1 <= 22`
     (`exact-level8-all-fast.json`, `run-level8-all-fast.log`). So (SG) holds at every `G_chi`.
   - The plain LLL basis fails only at `chi2` (192 classes, `H_1 = Z^54 + Z/2`, a row `(10, 24)`).

## Step 5. Decomposition

Assume (SG*) at every `Gamma(2N)`. Step 3 gives `d(Gamma(2N)) = 1/30`. Since `Gamma(2N) <= Gamma(N)`, (TA2)
gives `d(Gamma(N)) >= 1/30` for all `N`. So `d_inf = inf_N d(Gamma(N)) >= 1/30`. Also
`d_inf <= d(Gamma(2)) = 1/30`. Hence `d_inf = 1/30`.

Each instance is a single exact lattice computation at one level. A level where (SG*) fails, on every
basis tried, does not refute the conjecture, because (SG*) is sufficient but not necessary. Such a level
only shows that this route needs another argument there.
