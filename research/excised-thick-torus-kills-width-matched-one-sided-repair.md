---
rg: 2
id: excised-thick-torus-kills-width-matched-one-sided-repair
kind: claim
title: The excised thick torus has rectangle profile at most 2k and width defect zero, yet every one-sided regluing in either direction costs at least a ~ sqrt(d); width vectors cannot certify the doubly-wide repair
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this refutes one proof strategy for its permutation case (width matching plus one-sided regluing) and does not decide the statement. The family here is within rank k of a commuting pair.
  tall-cylinder-seams-reglue-within-quadratic-profile: that proves one-sided regluing within 176 rho^2 when one direction is locally tall, and its Theorem 2 kills one direction only (T_n is vertically tall). Here both directions are one cylinder of height 1, and both one-sided costs are unbounded at bounded profile.
  excised-square-kills-cone-local-slit-pair-repair: that excises a square from the n x n torus, whose vertical cylinder is tall; here the square is excised from a thick one-row torus, which is wide in both directions.
artifacts:
  - research/excised-thick-torus-kills-width-matched-one-sided-repair-proof.md
  - experiments/doubly-wide-2026-09-18/excised.py
  - experiments/doubly-wide-2026-09-18/onesided.py
  - experiments/doubly-wide-2026-09-18/prof.py
  - experiments/doubly-wide-2026-09-18/run3.py
  - experiments/doubly-wide-2026-09-18/summary.txt
---

**ESTABLISHED (unreviewed)** (`excised-thick-torus-kills-width-matched-one-sided-repair-proof`). This is an obstruction to the
step proposed at the end of `tall-cylinder-seams-reglue-within-quadratic-profile`: bound `sum_j h_j |w_j - w'_j|` by the
profile for a matchable width vector `w'`, then finish with the one-sided regluing of its Theorem 1.

**The family.** Take `a >= 2k + 1`, `W = a^2 + 1`, and the thick torus `T(W, a)` on `Z/W` with `b = +1` and `c = +a`.
This is one row of width `W` and height 1, closed up by a shift of `a`. Excise the `k` squares `0, ..., k-1`, so that
`b` and `c` skip them. Call the result `E = E(a, k)`, on `n = W - k` points.

**Theorem.**
1. *(Near-commuting.)* `(b_E (+) 1_k, c_E (+) 1_k)` is within rank `k` of `(b_T, c_T)` in each generator. So
   `Lambda_rect(E) <= 2k`, by Lemma B of `near-exact-tuples-saturate-linear-conversion-defect-proof`.
2. *(Doubly wide.)* `b_E` and `c_E` are both `n`-cycles. The horizontal decomposition is one cylinder of width `n` and
   height 1, whose top is glued to its own bottom, and the vertical decomposition is the same. So every width vector is
   matched, `sum_j h_j |w_j - w'_j| = 0` with `w' = w`, and Theorem 3 of the tall-cylinder node is vacuous. In both
   directions `w/tau = n`.
3. *(Horizontal one-sided cost.)* Every permutation `c'` commuting with `b_E` differs from `c_E` on at least `a` points,
   and `a` is attained. In the order of `b`, `c_E` is the 3-interval exchange with translations `a`, `2a - k` and
   `a - k` on intervals of lengths `n - a`, `k` and `a - k`.
4. *(Vertical one-sided cost.)* Every permutation `b'` commuting with `c_E` differs from `b_E` on at least
   `k(a - 1) + 1` points, and this is attained. In the order of `c`, `b_E` is translation by `-a + 1` on the `k(a-1)`
   points of an arc of length `ka`, translation by `-a` on the other points, and one exceptional point.

So at profile `<= 2k` both one-sided costs grow like `sqrt(d)`, while two-sided padding of the `k` holes costs `k`.

**Consequence (class killed).** No proof of the permutation case can go "adjust widths by column moves whose number is
controlled by `sum_j h_j |w_j - w'_j|`, then reglue one generator". On `E` the width defect is `0`, so no column moves
are made, and then each one-sided regluing, horizontal or vertical, costs at least `a`. The step asked for in the
tall-cylinder node is true on `E` for trivial reasons. But its intended combination with Theorem 1 cannot give a
uniform `F(K)`. What repairs `E` is `k` column insertions at the *positions* of the holes. Those positions are the
break points of the seam: `c_E` in item 3 has exactly 3 breaks, all at the holes. So any certificate has to see where
the columns go, not only how many there are.

**Computation** (`experiments/doubly-wide-2026-09-18/`). `run3.py` covers `a = 5, 7, 9, 11, 13` and `k = 1, 2, 3`.
- `rho_hat` is the maximum of `rank([b^s,c^t]-I)/(s+t)` over `s, t <= 2a`, a lower bound for `rho`. It lies between
  1.75 and 4.80, always `<= 2k`.
- Both decompositions are one cylinder `(n, 1)`.
- The exact one-sided optima are `a` (horizontal) and `k(a-1)+1` (vertical), with the one small exception
  `a = 5, k = 3` (vertical 11), which has `a < 2k+1`. Computed by assignment over rotation classes.

**What it leaves.** The doubly-wide case contains the *one-row case*: `b` an `n`-cycle, and `c` a `b`-interval exchange
with at most `N(1,1) <= 4 rho` breaks. The strongest next step is a two-sided statement there: a one-row pair with
profile `K` becomes a rotation after `O_K(1)` column insertions and deletions at its break points. This is the analogue
of Theorem 1 of the tall-cylinder node with the transversal taken as an interval of the row (zippered rectangles)
rather than a whole top. `E` shows that the insertions cannot be read off the width vector.
