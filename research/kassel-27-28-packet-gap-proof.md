---
rg: 2
id: kassel-27-28-packet-gap-proof
kind: route
title: Compare the clock commutator target with the forced permutation inverse
target: kassel-27-28-charge-the-explicit-omega-packet
requires: []
artifacts:
  - research/artifacts/kassel-27-28-clock-permutation-collision-2026-08-21.md
---

Solve (2.7) alone with a diagonal six-clock corrector and (2.8) alone with
`D=A^(-1)`.  For simultaneous approximate solutions, (2.8) gives
`||D-A^(-1)||_2=epsilon_8`; commutators with the fixed `x_alpha` are
`2`-Lipschitz.  The fixed commutator `[a,A^(-1)]=A^(-1)` and the clock target
`nu Z^(-1)` have zero mixed normalized trace, hence squared distance two.
Triangle inequality gives `epsilon_7+2epsilon_8>=sqrt(2)`, and Cauchy--Schwarz
gives the squared-energy floor `2/5`.

