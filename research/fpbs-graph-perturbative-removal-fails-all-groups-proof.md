---
rg: 2
id: fpbs-graph-perturbative-removal-fails-all-groups-proof
kind: route
title: One light step per redundant request, and relocated plans with no high-occupancy edges
target: fpbs-graph-perturbative-removal-fails-all-groups
requires:
  - fpbs-small-defect-reuse-on-high-occupancy-edges
  - fpbs-conditional-traffic-descent-bound
  - fpbs-traffic-defect-is-total-variation-loss
  - fpbs-bernoulli-noise-does-not-change-cost
artifacts:
  - research/artifacts/fpbs-graph-perturbative-removal-fails-all-groups-2026-09-17.md
---

P1 (artifact Proposition 3.1). With h_j = 1_{W_j} o pi, the traffic change of
variables of the descent bound writes the light traffic as the integral over
covered requests of u_s, the number of light steps on each path. The
high-occupancy lemma bounds this by (B' - r') + J'. A covered request with
u_s = 0 starts or ends a heavy occurrence, which has measure at most 2 eta' per
request. So |S| - r' - 2|S| eta' <= B' - r' + J'.

Graph stability (artifact Lemma 2.2). Summing the indicators of used label-h
copies at z gives at most m_h(z). If E[m_h | pi] <= 1/2, a copy of occupancy
above 1 - c sits over {|E[m'_h - m_h | pi]| > 1/2 - c}. Markov's inequality and
L1 contraction bound the occupancy mass there by 3 integral |m'_h - m_h| at
c = 1/4. With the heavy-mass bound of the high-occupancy lemma this gives
eta' <= 3 d_G + 4 delta.

P2 (artifact Lemma 4.1, Proposition 4.2). A countable separating Boolean algebra
gives a Borel proper colouring of the distance-< R graph. Greedy selection by
colour gives a Borel maximal R-separated set, and its Voronoi cells lie between
balls of radius ceil(R/2) - 1 and R - 1. The noise coordinate xi gives, given
Y_0, independent uniform permutations psi of all cells. psi is in the full group
and preserves measure. Take a near-optimal plan on Y_0 (formula (3)); its used
copies plus direct repairs form a generating graphing G of the same cost with
K maps. psi(G) has finitely many labels and the same cost, and it generates.
Truncating its shortest paths gives plans D_n with B(D_n) -> C(Y_0), which
equals C(Y) by the noise-cost claim. A realization of {z, z h} needs psi(y) = z
and psi(y g_i) = z h, or the reverse, with y in a cell of z or of z h. Each
case has conditional probability at most 1/(|C| (c_min - 1)), so
E[m_h | Y_0] <= 2K/(c_min - 1) <= 1/2 once c_min >= 4K + 1.

Combining, C + beta >= |S| - delta - 2|S|(3 d_G + 4 delta).
