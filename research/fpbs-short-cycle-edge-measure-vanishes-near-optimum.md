---
rg: 2
id: fpbs-short-cycle-edge-measure-vanishes-near-optimum
kind: claim
title: Short-cycle redundancy is quantitatively forced to large scales near the cost optimum
distinct_from:
  fpbs-priority-integral: that is the relative-cost integral bound for the candidate detour supports of the torsion constructions, above a fixed subrelation; this one is an unconditional surgery inequality on the whole unoriented edge space of any finite-cost locally finite graphing, in terms of shortest-cycle lengths
  fpbs-cycle-deletion-half-boundary: that is a finite combinatorial statement about edge boundaries after one deletion; this one is a cost inequality with no boundary content
artifacts:
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
  - research/artifacts/fpbs/responses/50_0909-211018.md
---

Let Phi be a finite-cost locally finite graphing generating an aperiodic relation R, and for an edge e let l(e) be the least length of a finite simple cycle through e, with reciprocal zero when there is none. Then C(R) <= c(Phi) - integral 1/l(e) dm(e). Equivalently, writing B_L for the edges lying on a cycle of length at most L and eps = c(Phi) - C(R), the edge measure satisfies m(B_L) <= L eps for every L >= 3. So an almost-minimizing graphing carries almost no edge measure on short cycles, and whatever redundancy remains is pushed to unbounded cycle length. The coefficient is sharp: a single L-cycle with uniform vertex measure has c = 1, C = 1 - 1/L, and integral 1/l dm = 1/L.

Status records a written deduction, not independent validation.
