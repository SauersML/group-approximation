---
rg: 2
id: fpbs-relative-cycle-diagonal-absence-split
kind: claim
title: The relative cycle operator's diagonal splits exactly into an absence term and a cycle-loss term
distinct_from:
  fpbs-relative-cycle-operator-descent: that constructs K and its total trace; this computes each diagonal entry and separates source absence from lost source cycles
  fpbs-graphing-cost-betti-cycle-dimension-identity: that is a dimension identity for one graphing; this is a pointwise conditional identity for the diagonal of the relative operator across a factor
artifacts:
  - research/artifacts/fpbs/docs/oblivious-occupancy-localization-obstruction.md
---

**ESTABLISHED.** Let pi:Y->X be a free p.m.p. factor of an infinite
countable group, Phi a finite-label generating source graphing, H its
conditional-support base graphing and K the averaged relative cycle
operator. For every base edge e, write rho_G(e) for the squared norm of
the projection of delta_e onto the closed span of finite cycles of G, and
p_e(x) for the conditional probability that e lies in Phi. Then

    <K_x delta_e,delta_e> = (1-p_e(x)) rho_H(e)
        + integral 1[e in Phi_y](rho_H(e)-rho_Phi_y(e)) dnu_x(y),

with both terms nonnegative. Consequently the localization premise of
`fpbs-relative-cycle-block-localization` forces
(1+2dM^2) times the crossing-edge integral of (1-p_e) rho_H(e) to tend to
zero. On block boundaries, source occupancy must be almost base-determined
wherever H has non-negligible cycle weight. Section 1 of the artifact
gives the proof.
