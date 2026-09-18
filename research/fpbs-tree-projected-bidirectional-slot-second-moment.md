---
rg: 2
id: fpbs-tree-projected-bidirectional-slot-second-moment
kind: claim
title: Bidirectional vertical runs and rigid collision counts extend the rank-two slot second moment of F_2 x Z with v = 2 to m = 13, 14, and to m = 12 for rigid decorations
distinct_from:
  fpbs-tree-projected-vertical-slot-second-moment: that allows one upward vertical step per slot and settles v = 2 for m = 15, 16, 17 only (its certificate fails at m = 14); this allows a vertical run of -1, 0 or +1 steps, shares vertical edges between up- and down-moving trails, refines the nonzero-offset capacity by an exact h' = 0 count, and for rigid decorations sharpens the collision count, which settles m = 13, 14 for all decorations and m = 12 for rigid ones.
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that is the open claim for every rigid decoration of every rank; this settles rank two, v = 2, uniform multiplicity for m = 12, 13, 14, and records that the heights-uniform count does not reach m <= 11.
  fpbs-tree-projected-rank-two-excursion-second-moment: that uses no vertical edges and settles v = 2 only for m >= 18; the ensemble here adds bidirectional vertical runs.
  fpbs-rigid-f2xz-certified-strict-thresholds: that certifies the single example S_rig (m = 3) by pattern-specific certificates; this is uniform over heights at m >= 12, and records that its ensemble cannot reach S_rig at all.
artifacts:
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/engine_r.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/certify_r.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/blockcheck_r.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/runr.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/pairx.c
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/anal.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/crit.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/lump.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/scan.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/showT.py
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/run_all.sh
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/cert_plain_R101_K1.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/cert_nzref_rigid_R101_K1.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/blockcheck_nzref_R101.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/blockcheck_nzref_rigid_R101.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/srig_obstruction.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/scan_float_small_m.txt
  - experiments/tree-projected-bidirectional-slot-second-moment-2026-09-18/scan_exact_nr_R101.txt
---

**ESTABLISHED (2026-09-18, computer-assisted, unreviewed)** through
`fpbs-tree-projected-bidirectional-slot-second-moment-proof`.

**Statement.** Let `Gamma = F_2 x Z` with free basis `{a, b}`. Let `S` be a finite
symmetric generating set with `pi(S) ⊆ {1, a^±1, b^±1}`, `|D_a| = |D_b| = m`, and
vertical part `{(1, c), (1, -c)}` for some `c != 0` (so `v = 2`).
1. If `m in {13, 14}`, then for arbitrary heights in `D_a`, `D_b` and arbitrary `c`,

   ```text
   p_c(Cay(Gamma,S))  <=  p_m  <  p*(m,2)  <=  p_{2->2}  <=  p_u ,
   ```

   with `p_13 = 5449/250000` and `p_14 = 10133/500000`.
2. If `m = 12` and the decorations are *rigid* (the four sets `D_a`, `-D_a`, `D_b`,
   `-D_b` are pairwise distinct up to translation), the same chain holds with
   `p_12 = 2947/125000`.

Here `p*` is the Ihara root of `fpbs-tree-projected-oriented-second-moment-thresholds`.
So `p_c < p_u` in both cases.

Together with `fpbs-tree-projected-vertical-slot-second-moment` (`m = 15, 16, 17`) and
`fpbs-tree-projected-rank-two-excursion-second-moment` (`m >= 18`), rank two with
`v = 2` and uniform multiplicity is settled for every decoration when `m >= 13`, and for
every rigid decoration when `m >= 12`.

**Mechanism.**
1. *Bidirectional runs.* Each slot now starts with a vertical run `r in {-1, 0, 1}`
   along `(1, c)` or `(1, -c)`, instead of an optional upward step. A vertical edge is
   recorded by its lower and upper heights, so an upward step of one trail and a
   downward step of the other can share an edge. A block still has at most 4 edges, so
   the criterion of the earlier claim carries over. The one-block weight is now exact,
   and larger: `3W(p*) = 1.0789` at `m = 12`, against `1.0633` at `m = 3`.
2. *Refined nonzero capacity (NZREF).* The LP map needs a bound on the total mass
   into nonzero offsets. For each term of that bound, the pairs with the same
   shared-edge equations and final offset `h' = 0` are counted exactly, when they
   form a pure identification of variables with an inequality forest and no
   internal coincidence. That count is then subtracted. It is valid for all
   decorations.
3. *Rigid collision count (RIGID).* Suppose a variable determined by the shared-edge
   equations has the form `y = a x + gamma`, with `x` a single free variable. For a
   rigid decoration, at most `m - 1` values `x` in `D_x` give `y` in `D_y`, whenever
   `a = +1` and the letters differ, or `a = -1` and the letters agree, or `|a| != 1`
   and the letters agree. The same holds in the two remaining unit cases when
   `gamma` is provably nonzero. Each inequality tree containing such an `x` is then
   counted `(m-1)` times fewer.
4. *Certificate.* The exact Collatz–Wielandt check of the earlier claim passes:
   * plain counting: margins `2.9e-3` (`m = 13`) and `8.2e-3` (`m = 14`);
   * NZREF with RIGID: margins `2.7e-3` (`m = 12`), `8.1e-3` (`m = 13`) and
     `1.27e-2` (`m = 14`).

   `blockcheck_r.py` compares the symbolic bounds with exact block sums on 24
   concrete decorations (20 of them rigid). The largest ratio of exact sum to bound
   is `0.986` (NZREF) and `0.987` (NZREF with RIGID), and the one-block weight
   matches exactly.

**Where it stops (recorded negative results).**
* *m <= 11, heights-uniformly.* The float spectral radii `rho_Phi / (3 w^2)` at `p*`
  are:

  | variant | m = 9 | m = 10 | m = 11 | m = 12 |
  |---|---|---|---|---|
  | NZREF, `K = 1` | | | 1.0081 | 1.0012 |
  | NZREF + RIGID, `K = 1` | | 1.0108 | 1.0035 | 0.9972 |
  | NZREF + RIGID, `K = 2`, runs `-2..2` | | 1.0098 | 1.0025 | 0.9964 |
  | NZREF + RIGID + multi-variable rigidity | 1.0195 | 1.0107 | 1.0034 | 0.9972 |

  None of the variants reaches `m = 11`. The remaining loss sits in two entries of the
  class transfer: `0 -> 0` (uniform `0.9446` against `0.9386` exact on a near-AP
  rigid decoration at `m = 12`) and the nonzero capacity of the generic row
  (`0.3545` against `0.3333`).
* *Below m = 12 the ensemble itself is fine.* On the near-AP rigid family
  `A = {0..m-2, m}`, `B = {0..m-3, m-1, m}`, `c = 1`, the exact per-decoration
  transfer (`pairx.c`, float spectral radius) passes at `p*` for each tested `m = 6, 7, 8, 10, 12, 14`.
  For example it is `0.9981` at `m = 6` and `0.9745` at `m = 10`. The class-lumped
  version of the same exact transfer passes from `m = 10`. So it is the
  heights-uniform count that fails at `m = 6..11`, not the ensemble.
* *The ensemble cannot reach S_rig.* For `S_rig` (`m = 3`, `c = 1`) with one excursion
  per slot, the exact pair transfer at `p*(3,2)` has spectral radius
  `rho_low ≈ rho_up > 1` for every run set:

  | runs | `{0,1}` | `{-1,0,1}` | `-2..2` | `-3..3` |
  |---|---|---|---|---|
  | `rho` at `p*` | 1.0691 | 1.0143 | 1.0085 | 1.0083 |

  So `E Z_N^2 / (E Z_N)^2 -> infinity` at `p*` (float, `srig_obstruction.txt`). The
  gain from longer runs saturates. In contrast, the first moment is no longer the
  obstruction: bidirectional runs give `3W(p*) = 1.063` (`{-1,0,1}`) and `1.079`
  (`-3..3`) at `m = 3`, where one upward step gave `0.983`.
