---
rg: 2
id: rips-segev-zero-divisor-via-special-marked-limits
kind: route
title: Approximate the Rips--Segev groups by special quotients and transfer the domain property
target: rips-segev-groups-satisfy-kaplansky-zero-divisor
requires:
  - rips-segev-groups-are-marked-limits-of-special-groups
  - marked-limits-of-special-groups-have-domain-group-rings
---

**Proof, given the premise.** Apply
`marked-limits-of-special-groups-have-domain-group-rings` to the marked limits
supplied by `rips-segev-groups-are-marked-limits-of-special-groups`. Every
field `k` gives a domain `k[G]`.
