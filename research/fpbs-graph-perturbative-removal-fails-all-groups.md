---
rg: 2
id: fpbs-graph-perturbative-removal-fails-all-groups
kind: claim
title: For every infinite finitely generated group, no removal by vanishing graph edits works after adding noise
distinct_from:
  fpbs-perturbative-reuse-removal-fails: that kills vanishing copy-metric edits on one factor of Z via two light steps per request; this kills vanishing edits in the orientation- and ownership-free graph metric for every infinite finitely generated group and every free factor after noise extension, via one light step per redundant request and relocated plans of occupancy at most 1/2
  fpbs-correlated-reuse-flags-removable: that asks for source-near-optimal plans with vanishing defect, which is cost preservation; this shows they cannot be reached from given relocated near-optimal plans by vanishing graph edits, in every group, without deciding cost preservation
  fpbs-small-defect-reuse-on-high-occupancy-edges: that confines small-defect reuse to high-occupancy copies; this adds the budget consequence that a small-defect near-optimal plan needs macroscopic heavy mass once |S| > C, and constructs plans with no high-occupancy edges
artifacts:
  - research/artifacts/fpbs-graph-perturbative-removal-fails-all-groups-2026-09-17.md
---

Let Gamma be an infinite finitely generated group, pi_0: Y_0 -> X a free factor,
Y = Y_0 x ([0,1]^Gamma, Leb) with pi = pi_0 o pr, and S a finite generating set
with e not in S and |S| > C(Y) (always available by adding a redundant
generator). For plans D, D' let d_G(D, D') = sum_h integral |m_h - m'_h|, where
m_h(z) counts the used copies realizing the edge {z, z h} in either
orientation, so d_G is at most twice the copy metric. Then there are finite
routing plans D_n with B(D_n) -> C(Y) such that every finite routing plan D'
with B(D') <= C(Y) + beta and J_pi(D') <= delta satisfies, for all n,

    d_G(D_n, D') >= ( |S| - C(Y) - beta - (1 + 8|S|) delta ) / (6|S|).

Two prerequisites combine. (P1) Any plan satisfies
B(D') >= |S| - J_pi(D') - 2|S| eta', where eta' is its heavy-occurrence mass,
because every request needs at least one light first step or starts on a
heavy occurrence. (P2) Relocating a near-optimal generating graph inside Borel
Voronoi cells of size at least 4K + 1 by a uniformly random permutation read
off the noise gives near-optimal plans with E[m_h | pi] <= 1/2 for every label.
The L1 stability of occupancy then bounds eta' <= 3 d_G + 4 delta.

Consequence: every graph-perturbative removal statement is false. Such a
statement asks, for arbitrary source-near-optimal plans, for small-defect
near-optimal plans at vanishing d_G distance. It fails for every infinite
finitely generated group, and for every family of factors that contains a noise
extension with a redundant request set. This answers the open scope question
of `fpbs-perturbative-reuse-removal-fails`. Cost preservation, macroscopic
rebuilds, factors not closed under noise, and request sets with |S| = C are
untouched. Written deduction over established claims, not independent
validation.
