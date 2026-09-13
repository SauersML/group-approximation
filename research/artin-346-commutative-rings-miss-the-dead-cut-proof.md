---
rg: 2
id: artin-346-commutative-rings-miss-the-dead-cut-proof
kind: route
title: Prove that commutative coefficients cannot kill both dead-edge sums of A(3,4,6)
target: artin-346-commutative-rings-miss-the-dead-cut
requires: []
artifacts:
  - research/artifacts/zp-artin-sigma1-dead-edge-rings-2026-09-13.md
---

Direct proof, written in the target's body and in artifact §6 (F1).

- Admissible partitions: an odd edge is never dead, so `b` and `c` lie on the same side.
- Conjugacy: `bcb = cbc` gives `(bc) b (bc)^{-1} = c`, so a commutative ρ has
  `ρ(b) = ρ(c)`.
- With `z = ρ(ab) = ρ(ac)`, the identity `(1 + z + z^2) - z(1 + z) = 1` shows that the two
  dead-edge sums generate the unit ideal.
- For Theorem 4.4 of arXiv:2501.08692v3: with `C` coefficients, `μ(φ(ab))` would have
  to be both `-1` and a primitive cube root of unity.
