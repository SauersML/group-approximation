---
rg: 2
id: deligne-third-floor-has-no-character-certificate
kind: claim
title: The uniform third cellular floor for Sp_4(Z) is a failure of dual closedness, since no continuous character of the profinite cochain space separates the Deligne class from the integral subgroup
distinct_from:
  deligne-schreier-complexes-have-a-uniform-third-cellular-floor: that is the floor itself; this proves that the floor, if true, cannot be certified by any continuous character (integral measured cycle) of the profinite cochain space, and that it is equivalent to non-dual-closedness of one closed subgroup.
  deligne-monomial-cover-models-have-a-detecting-cycle-floor: that shows finite detecting cycles grow along towers, so their bounds tend to 0; this treats the profinite limit, where every character certificate gives exactly 0, and adds a level-2 computation where the exact floor already exceeds every single-cycle bound.
  deligne-extension-dies-on-lagrangian-cantor-covers: that kills the class integrally on non-measure-preserving Cantor spaces; here the space is the profinite completion, where the class never dies and the question is metric.
artifacts:
  - experiments/deligne-third-floor-census-2026-09-17/census.py
  - experiments/deligne-third-floor-census-2026-09-17/bh_lifts.py
  - experiments/deligne-third-floor-census-2026-09-17/bh_relators.json
  - experiments/deligne-third-floor-census-2026-09-17/run_milp.py
  - experiments/deligne-third-floor-census-2026-09-17/run_s6.py
  - experiments/deligne-third-floor-census-2026-09-17/a0_milp.py
  - experiments/deligne-third-floor-census-2026-09-17/milp_small.log
  - experiments/deligne-third-floor-census-2026-09-17/milp_s6.log
  - experiments/deligne-third-floor-census-2026-09-17/a0_s6.log
  - experiments/deligne-third-floor-census-2026-09-17/parity.log
---

**ESTABLISHED** (`deligne-third-floor-no-character-certificate-proof`), items 1 and 2. Item 3 is a numerical
computation (HiGHS MILP, floating point, not rationally certified). Unreviewed.

## Setting

Notation of `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles` and of the floor node
`deligne-schreier-complexes-have-a-uniform-third-cellular-floor`.
- `Gamma = Sp_4(Z)` with a fixed finite presentation, `Y` its presentation complex, `k_c in Z` the lift exponent of
  the relator of the 2-cell `c` in the universal-cover lattice `Gamma~` (so `kappa = k` as a 2-cochain).
- `G` is the profinite completion of `Gamma`. `Gamma` acts on `G` by left multiplication, continuously and freely.
- `E = C^2(Y; C(G, R))`, the real 2-cochains of the Schreier "lamination" `Y x_Gamma G`, with the sup norm (max over
  2-cells and points of `G`). `delta : C^1(Y; C(G,R)) -> E` is the Schreier coboundary.
- `L = C^2(Y; C(G, Z)) + delta C^1(Y; C(G, R))`, an additive subgroup of `E`.
- `floor = inf_X mu_(1/3)(X)` over finite `Gamma`-sets `X`.

## Statement

1. **Profinite distance formula.** `floor = dist(kappa/3, L) = dist(kappa/3, cl L)` in `E`. So the floor node
   holds iff `kappa/3 notin cl L`.
2. **No character certificate.** Every continuous character `chi : E -> T` with `chi|L = 1` has
   `chi(kappa/3) = 1`. Equivalently, `kappa/3` lies in the dual closure `L^perp-perp`. Hence:
   - the floor node is **equivalent** to: *the closed subgroup `cl L` of the Banach space `E` is not dually closed,
     and `kappa/3` witnesses it*;
   - since the flagship `deligne-triple-cover-exact-mf-radical` implies the floor node, a proof that `cl L` is
     dually closed (or just that `kappa/3 in cl L`) **refutes the flagship** by permutation-with-phase models;
   - no argument of the form "one integral (measured) cycle on the lamination detects `kappa` mod 3" can prove the
     floor. The characters trivial on `L` are exactly the finite integral 2-cycles supported on finitely many
     leaves, and each leaf is the universal cover, where `kappa` vanishes.
3. **Level-2 census (numerical).** Exact MILP values of `mu = mu_(1/3)` and of the minimal detecting-cycle mass
   `A_0(X)` (integral cycle with `kappa = 1 mod 3`), with `D = D(Lambda)` of (L3):

   | `X` (Sp_4(F_2) = S_6 orbit) | points | `D` | `mu(X)` | `A_0(X)` | single-cycle bound `1/(3 A_0)` |
   |---|---|---|---|---|---|
   | point | 1 | 1 | 1/291 | 97 | 1/291 |
   | P^3(F_2) | 15 | 1 | 1/291 | 98 | 1/294 |
   | 2+4 partitions of 6 | 15 | 1 | 1/291 | 98 | 1/294 |
   | synthemes (2+2+2) | 15 | 1 | 1/291 | 98 | 1/294 |
   | Weierstrass points | 6 | 2 | 1/582 | 196 | 1/588 |
   | 3+3 partitions | 10 | 2 | 1/582 | 196 | 1/588 |

   `D` was computed by a parity MILP (no integral cycle with odd `kappa` iff `D = 2`), except for the synthemes,
   where `D = 1` is forced by `mu = 1/291 > 1/582`. So `mu(X) = 1/(291 D(X))` on every set solved. Here
   `||kappa_R||_cell = 1/97` on `Y` (LP over real cycles of the 8-cell complex; the integral 97-cycle with
   `kappa = 1` attains it). So `c_K = 1/582`.
   The value is the Kahler-proportional value `||kappa_R|| / (3D)` (take `f = kappa` if `D = 1`, `f = -kappa/2`
   if `D = 2`), and it meets the (K2) floor `c_K` exactly when `D = 2`. No non-Kahler class beats it there.
   Already at level 2 the exact floor exceeds every single-cycle certificate (`98 > 97`, `196 > 194`), which is the
   finite shadow of item 2.

## What this changes

- It kills, with a precise obstruction, every **linear** route to the floor: detecting cycles, their weak-* limits,
  and integral measured laminations. It extends the detecting-cycle node from towers to the profinite limit.
  Any proof must be non-linear, of the min-max type of (L1) with (K1)/(K2), and must see non-dual-closedness.
- It gives a new decomposition of the **refutation** side into a statement about one explicit closed subgroup of a
  `C(K)`-space: `kappa/3 in cl L`. By item 2, `kappa/3` is already in the dual closure, and on each leaf
  `kappa/3 = delta(beta/3)` exactly, with `beta` integral. The floor is precisely the claim that these leafwise
  solutions cannot be made continuous in `G` up to small error.
- The census is evidence **for** the floor at level 2: the residual non-Kahler classes, which exist there
  (`b_2(Gamma_2(2)) >= 7`), never lower `mu` below the Kahler value.

## Attempts
- **2026-09-19, swarm-0917-w14-w14-deligne-break: posed and proved (items 1, 2); census run (item 3).** Larger
  sets (ordered pairs of Weierstrass points, 30 points; Lagrangians over `F_2`) were started; the Lagrangian run hit
  its time limit at `mu <= 1/291` with no improvement found. Ordered pairs (30 points, 332 cells) hit the 1800 s
  limit with `1/588 <= mu <= 1/582`. Levels 3, 4, 5 were built (`census.py`) but not
  solved exactly: the MILP took 345 s at 164 cells and did not close LagF2 (150 cells) in 300 s.
