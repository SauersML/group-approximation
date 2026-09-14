---
rg: 2
id: ternary-corner-witness-support-proof
kind: route
title: The corner equation already holds in the subgroup algebra of its support
target: ternary-corner-witnesses-need-non-linear-sofic-support
requires:
  - linear-sofic-group-algebra-is-stably-finite
  - sofic-implies-linear-sofic-over-every-field
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

- **Restriction to `H`.** The product `c e_- b` involves only elements of `H`, so the equation holds in
  `F_3[H] eps_-`. Also `e_- != eps_-` there, because `1, z, w, zw` are distinct.
- **One-sided pair.** `A = e_- b + eps_+` and `C = c + eps_+` satisfy `CA = 1`. If also `AC = 1`, then
  `e_- b` is right invertible in `e_- F_3[H] eps_-`, which forces `e_- = eps_-`. So `F_3[H]` is not
  directly finite.
- **Conclusion.** Linear soficity over `F_3` would make `F_3[H]` stably finite, so `H` is not
  `F_3`-linear sofic. Sofic groups are linear sofic over every field, so `H` is not sofic.

Section 4 of the artifact.
