---
rg: 2
id: fpbs-tree-projected-chain-deficient-slot-second-moment
kind: claim
title: Chain-number collision caps and an exact pointwise generic row give strict thresholds on F_2 x Z with v = 2 for rigid letter sets far from two-progression unions, down to m = 5
distinct_from:
  fpbs-tree-projected-pollard-slot-second-moment: that settles every rigid decoration at m = 10, 11 with the non-AP gain m -> m-2 and a heights-uniform generic row; this replaces m - 2 by m - chi(D), bounds the Pollard pair count by m (m - chi), and certifies the pointwise generic row exactly, which settles m = 5..9 under a lower bound on the chain number chi.
  fpbs-tree-projected-rigid-decorations-strict-thresholds: that is the open claim for every rigid decoration of every rank; this settles rank two, v = 2, uniform multiplicity 5 <= m <= 9 for letter sets with enough chains, and records where the chain hypothesis cannot be dropped by this count.
  fpbs-rigid-f2xz-certified-strict-thresholds: that certifies the single example S_rig (m = 3) by pattern-specific certificates; this is uniform over heights for 5 <= m <= 9 and does not reach m = 3.
artifacts:
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/engine_h.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/certify_h.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/pwcheck.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/cert_chain.txt
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/pwcheck.txt
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/engine_w.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/buildw.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/runwpw.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/runwpw.txt
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/exact9.py
  - experiments/tree-projected-chain-deficient-slot-second-moment-2026-09-18/exact9.txt
---

**ESTABLISHED (2026-09-18, computer-assisted, unreviewed)** through
`fpbs-tree-projected-chain-deficient-slot-second-moment-proof`.

**Chain number.** For finite `D ⊂ Z` and `gamma != 0`, the `gamma`-chains of `D` are the
maximal runs `x, x + gamma, ..., x + l gamma` inside `D`. Let `chi(D)` be the least
number of `gamma`-chains over all `gamma != 0`. Equivalently,
`max_(gamma != 0) |D ∩ (D + gamma)| = |D| - chi(D)`. So `chi(D) >= 2` iff `D` is not an
arithmetic progression, which holds for every rigid set. `chi(D) >= k` iff `D` is not a
union of fewer than `k` progressions with one common difference. `chi(D) = |D| - 1` iff
`D` is a Sidon set.

**Statement.** Let `Gamma = F_2 x Z` with free basis `{a, b}`. Let `S` be a finite
symmetric generating set with `pi(S) ⊆ {1, a^±1, b^±1}`, `|D_a| = |D_b| = m`, and
vertical part `{(1, c), (1, -c)}` for some `c != 0`. Suppose the decorations are rigid
(the sets `±D_a`, `±D_b` are pairwise distinct up to translation). Suppose also that
`chi(D_a), chi(D_b) >= k(m)`, i.e. `|D ∩ (D + gamma)| <= m - k(m)` for both letters and
all `gamma != 0`, where

| `m` | `k(m)` | hypothesis `max r_D(gamma) <=` | `p_m` | `m p_m` | exact margin |
|---|---|---|---|---|---|
| 9 | 3 | 6 | 7807/250000 | 0.28105 | 2.38e-3 |
| 8 | 4 | 4 | 4377/125000 | 0.28013 | 1.10e-2 |
| 7 | 4 | 3 | 797/20000 | 0.27895 | 1.01e-2 |
| 6 | 4 | 2 | 46233/1000000 | 0.27740 | 1.26e-2 |
| 5 | 4 | 1 (Sidon) | 55051/1000000 | 0.27526 | 2.31e-2 |

Then for arbitrary such heights and arbitrary `c`,

```text
p_c(Cay(Gamma,S))  <=  p_m  <  p*(m,2)  <=  p_{2->2}  <=  p_u ,
```

so `p_c < p_u`. The margin is `1 - max_s Phi_s(y)/(L y_s)` in exact arithmetic
(`cert_chain.txt`).

At `m = 9` the hypothesis `chi >= 3` fails only when a letter set is a union of two
progressions with a common difference, e.g. `{0,...,6} ∪ {8,9}`. So for rigid
decorations with `m = 9` the open case is exactly the two-chain letter sets.

**Mechanism.** The ensemble, classes, LP map and criterion are those of the Pollard
claim. There are three changes, all pointwise in the heights.
1. *Chain collision caps.* A same-letter collision `y = x + gamma` with `gamma` provably
   nonzero confines `x` to `D ∩ (D - gamma)`, of size `m - chi_gamma(D) <= m - k`. The
   Pollard claim used `m - 2`.
2. *Pollard pairs with chains (`PNX`).* For `u != w` in one letter set and a set `S` of
   `m` values, `#{(u, w) : e(u - w) in S} <= Σ_(s in S, s != 0) r_D(s/e) <= m (m - k)`.
   The engine uses `min(P_neq(m), m (m - k))`. This matters for `m <= 8`, where
   `P_neq(8) = 44 > 32`.
3. *Exact pointwise generic row (`PW`).* For a generic start offset `h`, each gain on a
   single-variable condition is replaced by the exact count `R_kappa(h + j c)`, a sum- or
   difference-set representation number of the letter sets. The excursion-free pairs
   that land at `h' in {-c, 0, c}` are subtracted exactly, which gives the only 12
   negative coefficients. The generic row is then affine in 13 parameters that range
   over a box, and autocorrelation parameters are capped by `m - k`. The Pollard claim
   recorded this row as a float experiment. Here its supremum over the box is bounded
   in exact arithmetic by weak LP duality with rational multipliers.

`pwcheck.py` compares the pointwise row with exact block sums from the independent C
enumerator `pairx.c` on concrete decorations that satisfy each hypothesis. It also
asserts every parameter cap on them (`pwcheck.txt`). 33 decorations over the five
rows were tested. Every cap holds, and the largest ratio of exact mass to bound is
`0.9926`.

**Where it stops (recorded negative results, float or exact as marked).** These are
the same certificates with the next smaller `k` (exact ratio `max_s Phi_s/(L y_s)`, all
at the `p_m` above):

| `m` | `k` | ratio | letter sets excluded by the failing hypothesis |
|---|---|---|---|
| 9 | 2 | 1.00535 | all rigid sets allowed: this is the m = 9 rigid case |
| 8 | 3 | 1.00272 | |
| 7 | 3 | 1.00786 | |
| 6 | 3 | 1.01217 | |
| 5 | 3 | 1.01325 | |
| 4 | 3 (Sidon) | 1.00350 | |
| 4 | 2 | 1.05883 | |
| 3 | 2 | 1.05727 | includes `S_rig` |

* *The brief's step, pointwise landing mass `W(h)` in the test function
  `y(h) = a + b (r_Da + r_Db)(h)` (float, `engine_w.py`, `buildw.py`, `runwpw.py`, `runwpw.txt`).* The
  weighted landing mass was bounded pointwise by the same exact counts `R_kappa`,
  including the order-2 autocorrelations that enter `y`. The LP over `(a, b)` is then
  optimal at `b = 0`, with ratio `1.00532` at `m = 9`, the same as the pointwise row
  alone. The reason: the generic part of `W` is about `2.10 · 3w^2` per letter, and every
  `R_kappa` coefficient is at most `0.011 · 3w^2`. The mass that `W` puts on the heights where
  `r_Da + r_Db` is large comes from order-3 and order-4 convolutions
  `(1_D * 1_(-D) * 1_D * 1_(-D))(h)`. These are positive on all of `D - D + D - D`,
  and the engine's single-parameter gains cannot express them: one parameter per term
  gives order-2 data only. So this route does not reach `W` small where
  `r_Da + r_Db` vanishes. The worst letter sets for the heights-uniform count are the
  near-AP sets such as `{0,...,7,9}`, which have `chi = 2`. This is what motivated the
  chain hypothesis.
* *Per-decoration truth at `m = 9` (float, at `p*(9,2)`, `exact9.py`, `exact9.txt`).*
  The exact per-offset transfer of the same ensemble, from `pairx.c` block sums, has
  spectral radius over `3 w^2` of `0.973-0.979` for the `chi = 2` decoration
  `D_a = {0,...,7,9}`, `D_b = {0,...,6,8,9}` (`c = 1, 2, 5`), and `0.936-0.956` for
  five random rigid decorations. The same sums lumped into the four classes give
  `0.986-0.994` for the `chi = 2` decoration. So the ensemble and the lumping work at
  `m = 9` for `chi = 2`, and the loss is in the heights-uniform counting bound.

**Next step.** For `m = 9, chi = 2`, a letter set `D` has a difference `gamma_D` with
`r_D(gamma_D) = 7`. `r_D(g) = 7` forces `g = ±gamma_D`, so among the autocorrelation
parameters `r_D(h + j c)`, `|j| <= 1`, at most one per sign takes the value `7`.
Coupling the caps accordingly cuts the box in the pointwise row. The same coupling
applies to the collision factor on special classes when `gamma_D` is not a multiple
of `c`. The test is a float run of the coupled box.
