---
rg: 2
id: fpbs-tree-projected-pollard-slot-second-moment
kind: claim
title: Pollard sumset counts and non-AP collision counts extend the rank-two slot second moment of F_2 x Z with v = 2 to rigid decorations with m = 10, 11
distinct_from:
  fpbs-tree-projected-bidirectional-slot-second-moment: that settles m = 12 for rigid decorations (and m = 13, 14 for all) with one m -> m-1 gain per inequality tree; this keeps its ensemble and LP map and sharpens the counting bound by Pollard's theorem for pairs of free variables and by the fact that a rigid set is not an arithmetic progression, which settles m = 10, 11 for rigid decorations.
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that is the open claim for every rigid decoration of every rank; this settles rank two, v = 2, uniform multiplicity m in {10, 11}, and records that its heights-uniform count stops at m = 9.
  fpbs-rigid-f2xz-certified-strict-thresholds: that certifies the single example S_rig (m = 3) by pattern-specific certificates; this is uniform over all rigid heights at m = 10, 11.
artifacts:
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/engine_p.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/certify_p.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/blockcheck_p.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/runp.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/runpw.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/runwa.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/runwa2.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/pairx.c
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/anal.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/lump.py
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/cert_nonap_m10_11.txt
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/blockcheck_nonap.txt
  - experiments/tree-projected-pollard-slot-second-moment-2026-09-18/scan_float.txt
---

**ESTABLISHED (2026-09-18, computer-assisted, unreviewed)** through
`fpbs-tree-projected-pollard-slot-second-moment-proof`.

**Statement.** Let `Gamma = F_2 x Z` with free basis `{a, b}`. Let `S` be a finite
symmetric generating set with `pi(S) ⊆ {1, a^±1, b^±1}`, `|D_a| = |D_b| = m`, and
vertical part `{(1, c), (1, -c)}` for some `c != 0` (so `v = 2`). Suppose the
decorations are *rigid*: the four sets `D_a`, `-D_a`, `D_b`, `-D_b` are pairwise
distinct up to translation. If `m in {10, 11}`, then for arbitrary such heights and
arbitrary `c`,

```text
p_c(Cay(Gamma,S))  <=  p_m  <  p*(m,2)  <=  p_{2->2}  <=  p_u ,
```

with `p_10 = 28179/1000000` and `p_11 = 25673/1000000`. So `p_c < p_u`.

Together with `fpbs-tree-projected-bidirectional-slot-second-moment` (`m = 12` rigid,
`m = 13, 14` all), `fpbs-tree-projected-vertical-slot-second-moment` (`m = 15, 16, 17`)
and `fpbs-tree-projected-rank-two-excursion-second-moment` (`m >= 18`), rank two with
`v = 2` and uniform multiplicity is settled for every rigid decoration with `m >= 10`.

**Mechanism.** The ensemble (slot trails with one excursion and a vertical run
`r in {-1, 0, 1}` per slot), the offset classes `{-c, 0, c, G}` and the monotone LP
capacity map are those of the bidirectional claim, with its refined nonzero capacity
and its rigid `m -> m-1` gain. Two new counting refinements replace parts of the
inequality-forest bound. Both are pointwise in `h` and hold for every rigid decoration.
1. *Pollard pairs (POL).* If a determined variable `y = e1 x1 + e2 x2 + (earlier
   variables)` has two free variables, the pair `(x1, x2)` takes at most
   `P(m) = min_t [m t + (m-t)^2]` values instead of `m^2`. This is Pollard's inequality
   `Σ_s min(t, r_{A+B}(s)) >= t(|A| + |B| - t)` in `Z`. If moreover `x1, x2` have the
   same letter, opposite coefficients and `x1 != x2`, the bound is
   `P_neq(m) = min_t [m t + (m-t)(m-t-1)]`, since `r_{D-D}(0) = m` is all diagonal. At
   `m = 10` these are `75` and `70`, against `100` and `90`. Pairs are revealed in an
   order in which each `y` only involves revealed variables, and the engine takes the
   cheapest admissible family.
2. *Non-AP collisions (NONAP).* If `y = x + gamma` with `x`, `y` of the same letter and
   `gamma` provably nonzero, then `#{x in D : x + gamma in D} <= m - 2`. Equality `m - 1`
   would make the `gamma`-chains of `D` a single chain, so `D` would be an arithmetic
   progression, and an AP is symmetric up to translation, which rigidity excludes. The
   inequality tree of `x` then gains `m -> m-2`.

**Certificate** (`certify_p.py`, exact rationals, 1154 terms per `m`):

| `m` | `p_m` | `m p_m` | `3w` | `rho_Phi / 3w^2` (float) | exact margin |
|---|---|---|---|---|---|
| 10 | 28179/1000000 | 0.28179 | 1.07809 | 0.99953 | 4.72e-4 |
| 11 | 25673/1000000 | 0.28240 | 1.07857 | 0.99341 | 6.59e-3 |

`blockcheck_p.py` checks the symbolic bounds against exact block sums (independent C
enumerator `pairx.c`) for 7 rigid decorations at each of `m = 8, 9, 10, 11`. The
largest ratio of exact sum to bound is `0.9968` (`blockcheck_nonap.txt`), and the
one-block weight matches exactly.

**Where it stops (recorded negative results, float).**
* *m <= 9, heights-uniformly.* `rho_Phi / (3 w^2)` at `p*` (`scan_float.txt`):

  | variant | m = 8 | m = 9 | m = 10 | m = 11 |
  |---|---|---|---|---|
  | NZREF + RIGID (bidirectional claim) | | | 1.0108 | 1.0035 |
  | + POL + NONAP, `K = 1` (certified here) | 1.0151 | 1.0065 | 0.9995 | 0.9934 |
  | + pointwise-R generic row (PW), `K = 1` | | 1.0053 | 0.9984 | |
  | + PW, `K = 2` | | 1.0048 | | |

  PW makes the generic source row affine in the autocorrelations
  `R_kappa(h + j c) = #{(u, w) : s1 u + s2 w = h + j c}`, capped pointwise, and
  subtracts the exact landing mass of excursion-free pairs. It gains only `1.2e-3` at
  `m = 9`: once the row is a function of `R(h)` alone, the supremum over the box of
  admissible `R` values is still attained at one `h` with all caps active.
* *Where the remaining loss sits.* At `m = 9` the certifying ratio is set by the `0`
  row: `0 -> 0` is `0.948`, of which `0.9277` is the identity-type mass (exact for every
  decoration) and `0.0204` is decoration-dependent (Pollard-type energy terms and
  `R_t(±c)` terms). The generic class adds `0.3849 · y_G` with `y_G = 0.11`, which is
  forced by the generic row's return to `0`. The class lumping itself costs `0.0145` at
  `m = 10` on the rigid near-AP family (exact `0.9745`, lumped `0.9890`). A test
  function `y(h) = a + b (r_{D_a} + r_{D_b})(h)` on the generic class, instead of a
  constant, recovers about 80% of that loss on the exact near-AP operator
  (`0.9768`).
* *The h-dependent test function needs a pointwise landing bound.* With
  `y(h) = a + b S(h)`, `S = r_{D_a} + r_{D_b}`, every row needs the weighted landing
  mass `W(s) = Σ_(h' in G) T(s, h') S(h')`. Counting it with two extra variables
  `u - w = h'` (`runwa.py`) gives, divided by `3w^2` at `m = 9`, `W <= 4.68` from `0`,
  `6.44` from `±c` and `4.46` uniformly from the generic class. The last bound is the
  obstruction: at generic `h` with `S(h) = 0` the row needs
  `a (lam - T_GG) >= b W(h)`, and the uniform `4.46` is far above the true value
  (`W(h) = 0` for `h` far from `D - D`). With it the optimum is `b = 0`
  (`runwa2.py`: `1.00532`, no gain). A usable version must bound `W(h)` pointwise, by
  autocorrelations of order 3 and 4 at `h`, not uniformly.
