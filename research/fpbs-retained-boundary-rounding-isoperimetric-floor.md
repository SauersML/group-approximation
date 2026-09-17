---
rg: 2
id: fpbs-retained-boundary-rounding-isoperimetric-floor
kind: claim
title: Retained-boundary block rounding costs one plus excess boundary, so fully supported nonamenable certificates never localize
distinct_from:
  fpbs-oblivious-certificates-never-localize: that charges the diffuse cycle weight of base-oblivious occupancy against the M^2 factor and needs beta_1=0; this computes the rounding's output cost exactly and kills every occupancy function with fully supported nonamenable labels, with no cycle weights and no block-size factor
  fpbs-relative-cycle-block-localization: that is the open weighted boundary premise; this shows it fails for every certificate whose conditional support contains a fully supported nonamenable generating Cayley graph below the isoperimetric floor
  fpbs-relative-cycle-block-rounding-bound: that is an upper bound for the retained-boundary rounding; this is the exact cost of that rounding and its lower bound
  fpbs-cost-one-plans-have-heavy-traffic-tails: that forces traffic congestion in near-cost-one routing plans; this forces excess boundary in the tree-plus-crossing-edges rounding of any conditional support
artifacts:
  - research/artifacts/fpbs/docs/retained-boundary-isoperimetric-floor-2026-09-17.md
---

**ESTABLISHED.** Let Gamma act freely, H be a finite-label generating
graphing and E a measurable partition into finite blocks. Let H'(H,E)
keep every crossing H-edge and a spanning tree of each component of H
inside each block. This is the rounding of Theorem 6.1. Then

    c(H') = 1 + integral sum over components C of H|_B(x)
                of (|boundary_H C|/2 - 1)/|B(x)| dmu(x).

If H contains every S_0-edge a.e. for a generating S_0 whose Cayley graph
has degree d_0 and edge Cheeger constant h, then for every E

    c(H') >= F_0 = 1 + (1/2 - 1/d_0) h.

The proof uses Mader's edge-connectivity theorem. Consequences for a free
factor Y->X and a source Phi fully supported on S_0:

- premise (14) fails with (1+2dM^2)Tr(P_out K) >= F_0 - c(Phi) for all
  H-connected blocks of every size;
- the M-free bound c(H') <= c(Phi) + A + kappa also fails, where A is
  the crossing absence and kappa the interior disconnection;
- on F_2 x Z, which has fixed price 1, F_0 >= 5/3. So every near-optimal
  fully supported certificate misses (14) by 2/3 - o(1), whatever its
  occupancy.

The operator K is idle for this rounding. If near-optimal certificates
satisfy (14), then for each generating S_0 with F_0(S_0) > C(Y), the
occupancy of some label in S_0 must vanish exactly on a base-measurable
set of positive measure. Roundings that delete
crossing edges, such as the Section 7 retraction, are not covered.
