---
rg: 2
id: fpbs-perturbative-reuse-removal-fails
kind: claim
title: No removal by vanishing edits works on arbitrary optimal source plans, already for Z
distinct_from:
  fpbs-correlated-reuse-flags-removable: that asks for some source-near-optimal plans with vanishing defect, which is cost preservation; this shows such plans cannot be obtained from a given optimal plan by edits of vanishing measure, even where cost is preserved
  fpbs-binary-entropy-traffic-tail-bound: that gives optimal plans with vanishing flag entropy and defect one; this gives an optimal plan all of whose small-defect near-optimal neighbours are macroscopically far, with an explicit constant
  fpbs-cost-one-plans-have-heavy-traffic-tails: that forces congestion in near-cost-one plans of nonamenable groups; this bounds the used-edge distance from a given plan to every small-defect plan
artifacts:
  - research/artifacts/fpbs-perturbative-reuse-removal-fails-2026-09-17.md
  - experiments/fpbs-perturbative-reuse-removal-2026-09-17/parity_plan_verifier.py
---

Let X be the fair Bernoulli shift of Z, Y = X x Z/2 with T(x,i) = (sigma x, i+1)
and pi the projection; both actions are free of cost one. Let D be the plan
for the request y -> Ty with label +2 on {i = 0} and label +3 on {i = 1}, routed
y -> T^2 y -> T^4 y <- Ty for i = 0 and y -> T^3 y <- Ty for i = 1. Its edge
traffics are 3 and 2, so B(D) = 1 and J_pi(D) = 1. For plans D, D' let
d(D, D') = sum_g integral |n_g - n'_g|, where n_g(y) counts the used copies of
label g at y. Then every finite routing plan D' with B(D') <= 1 + beta and
J_pi(D') <= delta satisfies

    d(D, D') >= (1 - 2 beta - 81 delta) / 65,

and the same holds, less epsilon_0, for every plan within distance epsilon_0 of D.
The direct generator plan has B = 1, J = 0 and lies at distance 2.

Consequence: every *perturbative* removal statement is false. Such a statement
says that for a free factor pi and every sequence of source plans with
B(D_n) -> C(Y) there are plans D'_n with d(D_n, D'_n) -> 0, B(D'_n) -> C(Y) and
J_pi(D'_n) -> 0. That includes flag deletion, sparse sprinkling, rare repair
edges and local recoding applied to a given plan with vanishing edit measure.
It already fails on this Z factor with D_n = D. So it fails for any family of
groups or factor maps containing it. A per-plan removal theorem, the first
reducing form recorded under `fpbs-correlated-reuse-flags-removable`, must
make edits of measure bounded below by a fixed fraction of the budget.

The invariant is the base-conditional occupancy of labels, which edits move
only in L1. Every such procedure dies at the step where
`fpbs-small-defect-reuse-on-high-occupancy-edges` confines reuse to copies of
occupancy near one or to rare base regions. D has no such copies, and on Z
each request away from the small heavy set needs two single-use steps.

This does not refute cost preservation, the target claim or Fixed Price. Z has
fixed price, and correct plans exist far from D. Whether perturbative removal
fails for every infinite finitely generated group is not proved. Status
records a written deduction with an exact finite replay of D's traffic, not
independent validation.
