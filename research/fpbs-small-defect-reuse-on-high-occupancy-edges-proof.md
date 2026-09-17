---
rg: 2
id: fpbs-small-defect-reuse-on-high-occupancy-edges-proof
kind: route
title: Split the defect overlap at level c and bound occupancy changes by L1 contraction
target: fpbs-small-defect-reuse-on-high-occupancy-edges
requires:
  - fpbs-traffic-defect-is-total-variation-loss
artifacts:
  - research/artifacts/fpbs-perturbative-reuse-removal-fails-2026-09-17.md
---

The prerequisite gives J = sum_j integral min(a_j, b_j). On W_j = {a_j >= c,
b_j < c} the minimum is b_j, which is the conditional repeated traffic, so the
light repeated traffic is at most J. Heavy occurrences lie over {a_j < c},
where their measure is the integral of O_j, or over {a_j >= c, b_j >= c},
where min(a_j, b_j) >= c; by Markov that region has total measure at most J/c.
Light traffic splits as single use, at most B - r, plus light repeated use.

For stability, 1_{N'_j >= 1} <= n'_g for each copy of label g, so
a'_j < c forces E[n'_g | pi] > 1 - c and hence |E[n'_g - n_g | pi]| > 1/2 - c.
Integrate E[n'_g | pi] over that set F: at most mu(F)/2 plus the L1 norm of the
conditional difference, which is at most integral |n'_g - n_g| by L1
contraction, and Markov bounds mu(F). Section 2 of the artifact writes both
arguments in full.
