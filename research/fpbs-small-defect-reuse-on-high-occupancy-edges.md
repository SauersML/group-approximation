---
rg: 2
id: fpbs-small-defect-reuse-on-high-occupancy-edges
kind: claim
title: Small traffic defect confines repeated use to edges nearly determined by the base
distinct_from:
  fpbs-traffic-defect-is-total-variation-loss: that writes J as the overlap of absence and repeated use after projection; this derives from that overlap where a small-defect plan may carry reuse, and that the occupancy invariant moves only in L1 under edits
  fpbs-binary-entropy-traffic-tail-bound: that bounds J above by flag entropy and traffic tails; this is a structural consequence of J being small, with no entropy or tail hypothesis
artifacts:
  - research/artifacts/fpbs-perturbative-reuse-removal-fails-2026-09-17.md
---

Let D be a finite routing plan over a free factor pi:Y->X of a countable
group, with traffic N_j, a_j = P(N_j = 0 | pi), b_j = E[(N_j - 1)_+ | pi],
conditional occupancy O_j = 1 - a_j, uncovered mass r and budget B, and let
0 < c < 1. Put W_j = {a_j >= c, b_j < c} in X and call a used occurrence
(j,z) light when pi(z) is in W_j, heavy otherwise. Then

* the repeated traffic over light occurrences, sum_j integral over pi^{-1}W_j
  of (N_j - 1)_+, is at most J_pi(D);
* the heavy occurrences have measure at most
  sum_j integral over {a_j < c} of O_j, plus J_pi(D)/c;
* the total light traffic is at most (B - r) + J_pi(D).

Occupancy is stable under edits: let n_g(y) count the used copies of label g
at y. If E[n_g | pi] <= 1/2 almost everywhere and D' is another plan, then for
0 < c < 1/2 the copies of label g in D' satisfy
sum_j integral over {a'_j < c} of O'_j <= (1/(1-2c) + 1) integral |n'_g - n_g|,
and if n_g = 0 the bound is integral |n'_g - n_g|.

So a plan of small defect does almost all its repeated use on copies whose
occupancy given the base exceeds 1 - c, or over rare base regions, and plans
obtained by small edits of a plan whose labels are split by independent noise
have almost no such copies. This is a written deduction (Section 2 of the
artifact), not independent validation. It does not by itself prove or refute
cost preservation.
