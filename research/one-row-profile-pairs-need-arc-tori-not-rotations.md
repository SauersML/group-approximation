---
rg: 2
id: one-row-profile-pairs-need-arc-tori-not-rotations
kind: claim
title: One-row permutation pairs of rectangle profile 3 can be unboundedly far from every single-row commuting pair; the one-row target is a bounded arc-torus, an exact reformulation of permutation distance
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this refutes one proposed step for its one-row permutation case (profile K gives a rotation after O_K(1) column insertions or deletions) and replaces it by an equivalent multi-row target. It does not decide the statement.
  excised-thick-torus-kills-width-matched-one-sided-repair: that kills width matching plus one-sided regluing using E(a,k), which IS repaired by column insertions at its breaks (theta = beta + gamma below). The family here has profile at most 3 and no single-row repair at all.
  tall-cylinder-seams-reglue-within-quadratic-profile: that reglues one locally tall direction; here b is a single cycle of length n, so neither direction is tall, and the repair cuts the row instead of regluing seams.
artifacts:
  - research/one-row-profile-pairs-need-arc-tori-not-rotations-proof.md
  - experiments/one-row-2026-09-18/verify.py
  - experiments/one-row-2026-09-18/prof.py
  - experiments/one-row-2026-09-18/repair.py
  - experiments/one-row-2026-09-18/qres.py
  - experiments/one-row-2026-09-18/scan3b.py
  - experiments/one-row-2026-09-18/scan400.txt
  - experiments/one-row-2026-09-18/periods.py
  - experiments/one-row-2026-09-18/regions.py
  - experiments/one-row-2026-09-18/summary.txt
---

**ESTABLISHED (unreviewed)** (`one-row-profile-pairs-need-arc-tori-not-rotations-proof`). This settles, negatively,
the step proposed at the end of `excised-thick-torus-kills-width-matched-one-sided-repair`. It then states the
corrected one-row target, which is equivalent to the permutation case of the open statement for one-row pairs.

**Setting.** A *one-row pair* is `b = +1` on `Z/n` together with any permutation `c` of `Z/n`. Write
`D_t(x) = c^t(x) - x` and `B_t = {x : c^t(x+1) != c^t(x) + 1}`, the break set of `c^t`. A *single-row repair* is a
commuting permutation pair `(b', c')` on `Z/n` plus padding `P` in which `b'` is one cycle, for example a rotation after
inserting or deleting columns. Its cost is `max(rank(b' - b (+) beta), rank(c' - c (+) gamma))`, with the padding
permutations `beta` and `gamma` chosen as well as possible.

**Theorem.**
1. *(Break lemma.)* `Lambda_rect(b, c) <= sup_t |B_t|`.
2. *(Single-row lower bound.)* Every single-row repair costs at least `min(|Fix c|, n - |Fix c|) / 2`.
3. *(The family.)* Take `alpha, beta, gamma >= 1` with `n = alpha + beta + gamma`. Let `c = S` fix `A = [0, alpha)` and
   swap the arcs `B = [alpha, alpha+beta)` and `C = [alpha+beta, n)`. Then `|B_t| <= 3` for all `t`, so
   `Lambda_rect <= 3`. Cutting `b` into the two rows `A` and `B u C` gives a commuting pair at cost 1. Every
   single-row repair costs at least `min(alpha, beta+gamma) / 2`, which is unbounded.
4. *(Arc-torus reformulation.)* Let `delta_perm` be the least cost of a commuting *permutation* pair. An
   `(m, e)`-*arc-torus* for `(b, c)` is a commuting permutation pair `(b', c')` on `Z/n (+) P` such that:
   - `b'` differs from `b (+) beta` in at most `m` points; so each `b'`-cycle is a cyclic concatenation of old arcs and
     padding runs, with at most `m` arcs in total;
   - `c'` differs from `c` at most at `e` old points; `c'` carries rows to rows by translations.

   Then `delta_perm <= max(m, 2e)`. Conversely, a pair at cost `delta_perm` is a `(2 delta_perm, 2 delta_perm)`-arc-torus.
5. *(Twist theta = beta + gamma.)* Put `c = R_theta o S`, which is the one-cylinder H(2) diagram with twist `theta`. At
   `theta = beta + gamma` there is a single-row repair: insert `beta` columns after `n - 1`, set `c' = +(beta+gamma)` on
   `Z/(n + beta)`, and change `c` only on `B`. So `m = 2` and `e = beta`. The pair `E(a, k)` of the excised-torus node is
   the case `alpha = n - a`, `beta = k`, `gamma = a - k`.

**What this kills.** The one-row step "profile `K` gives a rotation after `O_K(1)` column insertions or deletions at the
breaks" fails already at profile 3 (item 3). So would any argument whose output is a single row, for example
Rauzy–Veech induction with an interval of the row as the only transversal. A repair must be allowed to *cut* the row
into several rows. In item 3 the cuts are at the breaks `alpha - 1` and `n - 1`.

**Data** (`experiments/one-row-2026-09-18/summary.txt`; `rho^` counts moved points, so it lies between `Lambda` and
`2 Lambda`).
- *Resonant twists `theta = n/q`.* `rho^` is about `2q` (5.81, 8.37, 10.59, 13.85 and 15.79 for `q = 2, 3, 4, 6, 8`). So
  these resonances are not bounded-profile counterexamples.
- *Generic twists at `beta = 1`.* `rho^ ~ sqrt(n)/2`. So a bounded profile forces an arithmetic resonance of the twist.
- *The pair `(n, theta, alpha, beta, gamma) = (400, 157, 229, 75, 96)`.* Here `rho^ = 9.91` and `c` is a 400-cycle.
  `c^3 = b^-4` holds on 212 points (three arcs), and `c^2 = b^10` holds on 150 points (the arcs `B` and `c^-1(B)`).
  So it is two thin arc-tori in diagonal directions, and a repair of about 60 is expected (ratio about 6).
  Block-insertion repairs alone cost ratio 17.

**Corrected next step.** For one-row pairs, show that `Lambda_rect <= K` gives an `(m, e)`-arc-torus with
`m, e <= F(K)` whose cuts lie in `U_{|j| <= O(K)} c^j(B_1)`. The candidate mechanism is that each `B_t` with
`t <= O(K)` is a union of short `c`-orbit segments of breaks. Without the clause on where the cuts lie, item 4 makes this
equivalent to the permutation case of the open statement for one-row pairs. The data fit the full conjecture. The reduction of the general doubly-wide case to
one-row pairs is not attempted here.
