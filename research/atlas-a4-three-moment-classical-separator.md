---
rg: 2
id: atlas-a4-three-moment-classical-separator
kind: claim
title: Two A4 contexts and collision 19243 define a three-moment separating hyperplane for all classical alignment mixtures
artifacts:
  - experiments/atlas_triangle_19243_two_context_gap.py
  - experiments/atlas-word-19243.json
distinct_from:
  atlas-a4-classical-mixture-trace-separator: that separator uses all thirty pair-cube moments; this claim uses only the two-context hitting core and the collision moment.
---

Let `u,v` be packet tree indices `6910,6940` from
`atlas-a4-two-context-collision-gap`, and let `q=q_19243`.  For every convex
mixture `tau_nu` of inner and outer regular A8 chart-alignment trace states,

```text
||u-1||_(2,tau_nu)^2
 + ||v-1||_(2,tau_nu)^2
 + ||q-1||_(2,tau_nu)^2
 >= 2.                                                  (A4-3M-SEP)
```

Equivalently,

```text
Re tau_nu(u) + Re tau_nu(v) + Re tau_nu(q) <= 2.       (A4-3M-HYP)
```

Thus the relevant classical convex hull is already separated from the perfect
point `(1,1,1)` in **three scalar coordinates**.  No information from the
other twenty-eight A4 contexts is needed at the final soundness step.

## Attempts

- Apply `atlas-a4-two-context-collision-gap` pointwise to each alignment and
  then use affinity of normalized-HS squared defect under convex mixtures; the
  companion proof route records the two-line argument.
