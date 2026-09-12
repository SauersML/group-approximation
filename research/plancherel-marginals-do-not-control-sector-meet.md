---
rg: 2
id: plancherel-marginals-do-not-control-sector-meet
kind: claim
title: Equal Plancherel sector masses permit either one shared deficit or the full sum
distinct_from:
  canonical-finite-packet-data-stop-at-scalar-overlaps: that studies multiplicity-reservoir ownership after masses and scalar overlaps are fixed; this shows already that the one-sector marginals alone do not determine the accepting meet.
  common-meet-local-sectors-pay-one-deficit: that proves the analytic benefit of a small actual meet deficit; this gives the exact finite-group models showing that benefit must be authenticated.
---

**ESTABLISHED SHARPNESS.**  Fix `m` and a finite abelian group `K` of order
`N>=m`.  In the canonical group trace on `C[K]`, every character atom
`e_chi` has trace `1/N`.  There are two families of projections with the
same individual Plancherel masses

```text
tr(q_c)=1-1/N             (1<=c<=m),                      (PMM1)
```

but opposite meet behavior:

1. choosing one atom `e` and setting every `q_c=1-e` gives
   `tr(1-meet_c q_c)=1/N`;
2. choosing distinct atoms `e_1,...,e_m` and setting `q_c=1-e_c` gives
   `tr(1-meet_c q_c)=m/N`.

Hence the codimension union bound is attained exactly by a canonical finite
Plancherel packet, while literal sharing improves it by the full factor
`m`.  No argument using only the individual masses `alpha_c` can claim the
improvement.  A common-ghost approach to
`canonical-high-density-local-sector-groupifier` must impose and verify the
overlap/identity of the rejected atoms (or directly compute the meet); it
cannot infer sharing from equal packet types or equal canonical masses.

