---
rg: 2
id: clifford-cover-algebra-splitting-proof
kind: route
title: Split the modular group algebra over the central involution
target: clifford-cover-group-algebra-splits-into-wreath-and-skew-ring
requires:
  - rf-lamps-preserve-stable-finiteness-for-arbitrary-actions
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

Artifact Section 3, Proposition 3.1.
- `(1 +- eps)/2` are orthogonal central idempotents summing to `1`, since `2` is invertible mod 3.
- The `+` summand is `F_3[W]`.
- On the `-` summand, `eps = -1` turns the extension relations into the displayed lamp relations, and
  `G` fixes `eps`.
- `F_3[W]` is stably finite, because the base `G` is residually finite. So direct finiteness of the
  product is decided on `A_S`.
