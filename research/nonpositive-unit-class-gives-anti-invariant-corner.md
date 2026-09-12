---
rg: 2
id: nonpositive-unit-class-gives-anti-invariant-corner
kind: route
title: Halving through the diagonal endomorphism turns a nonpositive unit class back into the ternary corner
target: ternary-anti-invariant-swap-corner-is-full
requires:
  - ternary-anti-central-unit-class-is-nonpositive
  - twisted-leavitt-corner-fullness-equals-absence-of-k0-states
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

- **Identification.** At `(q, d, m) = (3, 2, 2)` the Leavitt-visible factor is `S_-`, with
  `e_H = e_-` and `g = w` (`ternary-anti-invariant-corner-is-the-q3-m2-cyclic-case`).
- **Reduction to k = 1.** A nonpositive multiple `k[eps_-] <= 0` gives `[eps_-] <= 0`.
- **Conclusion.** Item 4 => item 1 of the equivalence claim then solves `c e_- b = eps_-`.
- **Mechanism.** `psi(x) = e_- delta(x)`, with `delta(h) = s0 h t0 + s1 h t1`. This `delta` commutes
  with `w` and fixes `z`.

This reverses `anti-invariant-corner-gives-nonpositive-unit-class`. Section 7.3 of the artifact.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 25 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
