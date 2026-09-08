---
rg: 2
id: higman-rational-word-coefficient-proof
kind: route
title: Evaluate the four relators on one diagonal and one symmetric rational unitary
target: higman-hs-word-coefficient-exceeds-nine-fifths
requires: []
artifacts:
  - research/artifacts/higman-hs-word-coefficient-lower-bound.md
  - research/artifacts/higman-hs-word-coefficient-witness.json
---

Set the middle two generators to I_2. For the first take
`diag((-60+91i)/109,(-60-91i)/109)`; for the last take
`(12 I_2+35 i X)/37`, where X exchanges the two coordinates. The two
Pythagorean identities prove exact unitarity.

The first two relators vanish. The third energy is 50/37 and the fourth
is 628372082/1772894701, while the marked energy is 338/109. Dividing
the marked energy by the positive relator sum gives
2748800041/1512087866. Every coefficient in a universal bound must be
at least that large. The artifact derives the trace formula explicitly;
the supplied exact matrix verifier independently replays the entries.
