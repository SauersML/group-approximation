---
rg: 2
id: tall-cylinder-seams-reglue-within-quadratic-profile
kind: claim
title: A permutation pair whose non-torus horizontal cylinders are locally tall (width at most the least height at their seams) is within rank 176 rho^2 of a commuting pair with b unchanged; the width/height ratio term is sharp for one-sided regluing
distinct_from:
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement; this proves its permutation case, with a polynomial bound, on the class of pairs having a locally tall cylinder direction, and does not prove the statement.
  seam-surface-forces-neutral-relocation-in-self-bound-lemma: its Proposition 3 is the one-cylinder case (height at least the circumference); here any number of cylinders share seams, widths may differ, and the height condition is local.
  cone-excess-transfer-reduces-donor-lemma-to-self-bound: that reduces to a local lemma at self-bound cone points and iterates to an exponential F; here the whole surface is repaired at once in the tall class, with no iteration.
  excised-square-kills-cone-local-slit-pair-repair: that shows cone-local slit pairs are long on the excised square; here the same surface shows that any one-sided (b fixed) regluing costs at least 2(n-1), matching the width/height term.
artifacts:
  - research/tall-cylinder-seams-reglue-within-quadratic-profile-proof.md
  - experiments/cylinder-seams-2026-09-18/seams.py
  - experiments/cylinder-seams-2026-09-18/summary.txt
  - experiments/cylinder-seams-2026-09-18/onerow.py
---

**ESTABLISHED (unreviewed)** (`tall-cylinder-seams-reglue-within-quadratic-profile-proof`). Elementary counting plus
a bipartite regluing. It proves the permutation case of `z2-bounded-rectangle-profile-forces-near-commuting` on a new
class, with `F(K) = 176 K^2`, and it is the multi-cylinder, shared-seam form of Proposition 3 of
`seam-surface-forces-neutral-relocation-in-self-bound-lemma` asked for there.

**Setting.** Read a permutation pair `(b, c)` on `d` points as a square-tiled surface (`b` = right, `c` = up), and let
`rho = Lambda_rect(b, c)`. The rows are the `b`-cycles. A *cylinder* is a maximal chain of rows `r_1, ..., r_h` with
`c` mapping `r_i` onto `r_(i+1)` `b`-equivariantly. Chains that close up are flat torus components and already
commute. Let `C_1, ..., C_m` be the other cylinders, with widths `w_j` and heights `h_j`. The *seam* is `c` on their
top rows: a bijection `sigma` from top points to bottom points. For each `j` let `tau_j` be the least height among
`C_j` and every cylinder that the seam joins to the top or the bottom of `C_j`.

**Theorem 1 (seam regluing).** There is `c'` commuting with `b` that differs from `c` only on top rows, with
`#{x : c'(x) != c(x)} <= min(2 sum_j w_j, 96 rho^2 + 20 rho sum_j w_j / tau_j)`.
In particular, if every non-torus cylinder is *locally tall* (`w_j <= tau_j`), then `(b, c')` is a commuting pair
with `rank(c' - c) <= 176 rho^2` and `b' = b`. Taking `c` for `b`, the same holds for the vertical direction.

**Ingredients.**
- *Few cylinders.* Every top row contains a break `z` (`c b z != b c z`), so `m <= #defects <= 2 rank([b,c]-I) <= 4 rho`.
- *Width lemma.* Take `s = w_j`, so `b^s` fixes `C_j` pointwise, and `t = tau_j`. Every column over a top point `z`
  whose target cylinder has width not dividing `w_j` gives `t` moved points of `[b^s, c^t]`. Hence
  `u_j <= 2 rho (1 + w_j / tau_j)`. The same holds from the bottom side with `c^(-t)`. So the number `U` of seam points
  that join cylinders of different widths is at most `2 rho (2m + sum_j w_j/tau_j + sum_j w_j/tau_j)`.
- *Offset lemma.* On the points of `C_j`'s top that go to a cylinder of the same width, average the moved points of
  `[b^s, c^tau_j]` over `0 <= s < w_j`. The largest class with a common target and rotation offset has size `m*_j`
  with `w_j - m*_j <= 2 rho (2 + w_j / tau_j)`, unless more than half of the top is in `U`.
- *Regluing.* A class of more than half of a top determines its target, and two tops cannot share one. Glue these tops
  by their class rotation, and complete by any width-preserving bijection (the width counts agree, since tops and
  bottoms are the same cylinders). The cost is at most `2 sum_j (w_j - m*_j)`.

**Theorem 2 (the ratio term is needed for one-sided regluing).** Let `T_n` be the `n x n` torus with one square
excised. It has `rho <= 2` (`excised-square-kills-cone-local-slit-pair-repair`) and distance 1. Its horizontal
cylinders are `A` (width `n`, height `n-1`) and `B` (width `n-1`, height 1), so `w_B/tau_B = n - 1`. Every `c'`
commuting with `b` differs from `c` on at least `2(n-1)` points. The only row of length `n-1` must be mapped onto
itself, whereas `c` sends it into `A`, and the `n-1` points of `A` that `c` sends into it must be sent elsewhere. Hence no bound of the form `f(rho)` alone holds for regluings
that keep `b`. The short-cylinder case needs two-sided moves, as in the distance-1 repair of `T_n`.

**Theorem 3 (height gap at mismatched seams).** Suppose the seam sends `a` top points of `C_j` into the bottom of
`C_beta`, where `w_beta != w_j`. Then `a min(h_j, h_beta) <= 2 rho (max(w_j, w_beta) + min(h_j, h_beta))`. Take
`s = w_j` (or `s = w_beta`, from the bottom side with `c^(-t)`, if `w_beta` divides `w_j`) and
`t = min(h_j, h_beta)`. Every orbit counted then crosses one seam and is moved by `[b^s, c^t]`. In particular, if
`a >= max(w_j, w_beta)/2 >= 4 rho`, then `min(h_j, h_beta) <= 8 rho`. A large width mismatch therefore forces a
genuinely short cylinder, of height `O(rho)`. This is the height side of the tall/short dichotomy for Proposition 3.

**What it gives.** Together with the vertical direction, every permutation pair with `Lambda_rect <= K` is within
`176 K^2` of a commuting pair unless *both* its horizontal and its vertical decompositions contain a locally wide
cylinder (`w_j > tau_j`). This replaces, on that class, the `exp(O(K^2 log K))` iterate of
`cone-excess-transfer-reduces-donor-lemma-to-self-bound` by a quadratic bound, with no cone-point lemma needed. The
seam surfaces `S(H, tw)` of `seam-surface-forces-neutral-relocation-in-self-bound-lemma` with `H >= 6` and the slit
tori are in the class.

**Computation** (`experiments/cylinder-seams-2026-09-18/seams.py`). There were 450 random multi-cylinder surfaces
(up to 4 cylinders, widths up to 7, heights up to 9, piecewise-translation seams with every top broken). On each,
the script computes `rho_hat` (the maximum of `rank([b^s,c^t]-I)/(s+t)` over `s <= 8`, `t <= 10`, a lower bound for
`rho`), the exact optimal one-sided cost (an assignment over rows with rotations), and the proof's regluing cost.
- Every inequality of the proof held at the tested `(s, t)`: `m <= 4 rho_hat`, the width lemma, the offset lemma,
  and `opt <= alg <= rho_hat^2 (96 + 80 W/H)`.
- On the 99 tall surfaces, `alg <= 1.57 rho_hat^2`.
- On `T_n` (`3 <= n <= 9`), `rho_hat < 2` and the exact one-sided optimum is `2(n-1)`, as Theorem 2 says.
- The height gap `(5)` held for every mismatched pair of cylinders.
- `onerow.py` treats the single-row surfaces `b` = rotation of `Z/6 lambda`, where `c` reverses the intervals
  `(lambda, 2 lambda, 3 lambda)`. For `lambda = 1, 2, 4, 8, 16` it finds `rho_hat` rising from 1.33 to 1.94, while the
  cost with `b` fixed is `d1 = 3 lambda`. This is a second family on which the one-sided cost is unbounded. It is not a
  counterexample, since the vertical decomposition is one cylinder of width 6 and height `lambda` (checked for
  `lambda <= 8`), which is tall once `lambda >= 6`.

**What it leaves.** The permutation case is now open only for surfaces with a locally wide cylinder in both
directions. The next step is a two-sided width adjustment. Padding or deleting one column of a cylinder of height
`h` costs `O(h)` in each generator. The step is to show that the profile bounds `sum_j h_j |w_j - w'_j|` for some
matchable width vector `w'`, as it does on `T_n`, where the adjustment is one square of `B`.
