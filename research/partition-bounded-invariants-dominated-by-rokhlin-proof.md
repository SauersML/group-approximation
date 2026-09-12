---
rg: 2
id: partition-bounded-invariants-dominated-by-rokhlin-proof
kind: route
title: Take the infimum of the partition bound over generating partitions
target: rokhlin-entropy-is-the-largest-partition-bounded-invariant
requires: []
artifacts:
  - research/artifacts/conjugacy-invariants-and-partition-bounds-2026-09-12.md
---

Section 2 of the artifact.
- Rokhlin entropy is the infimum of `H(Q)` over generating partitions `Q`. So it is bounded by
  each of them, and it is invariant because isomorphisms carry generating partitions to generating
  partitions.
- A partition-bounded invariant is below every `H(Q)`, hence below the infimum.
- Saturation `I(A^G) = log |A|` gives `log |A| <= h^Rok(A^G) <= H(time-zero partition) = log |A|`.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 2.2 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Saturation on `A^G` applies for infinite `G`, where the Bernoulli action is ergodic.
