---
rg: 2
id: artin-346-dead-character-outside-sigma1-by-rank-two-rep-proof
kind: route
title: Apply the dead-edge ring obstruction to A(3,4,6) with an explicit 2x2 representation
target: artin-346-dead-character-outside-sigma1-by-rank-two-rep
requires:
  - artin-sigma1-dead-edge-ring-obstruction
artifacts:
  - research/artifacts/zp-artin-sigma1-dead-edge-rings-2026-09-13.md
---

Artifact §5. First check the three Artin relations for
`ρ(a) = M^{-1}`, `ρ(b) = -M`, `ρ(c) = M y`:

- `(ab)^2 = (ba)^2`: both sides map to `I`.
- `(ac)^3 = (ca)^3`: both sides map to `I`, since `y^3 = I`.
- `bcb = cbc`: `M^2 y M = -M y M^2 y`, i.e. `M y M = -y M^2 y`, checked entrywise with
  `ω^2 = -1 - ω`.

Next, the two dead-edge sums vanish: `I + (-I) = 0` and `I + y + y^2 = 0`. The cut
`{a} | {b, c}` has live vertices on both sides and only dead cross edges, so the
obstruction applies.
