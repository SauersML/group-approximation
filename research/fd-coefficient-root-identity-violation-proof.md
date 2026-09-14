---
rg: 2
id: fd-coefficient-root-identity-violation-proof
kind: route
title: Push the model through a finite general linear group and act by the regular representation
target: fd-represented-coefficients-violate-two-root-identities
requires: []
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Complete proof: artifact Section 4.

- **The finite group.** `EL_3(S) -> GL_3(M_n(F_p)) = GL_(3n)(F_p)` has finite image `H`, and
  `x_ab(1)` maps to `h_ab = 1 + I_n (x) E_ab`.
- **The rank model.** The left regular representation of `H`, embedded by `a -> (a (x) I_m)_m`,
  is a rank model of `EL_3(S)`.
- **The product is nonzero.** `(h_23 - 1)(h_12 - 1) = h_23 h_12 - h_23 - h_12 + 1` has four
  distinct group elements, so it is nonzero in `F_p[H]`, and left multiplication by it has
  positive normalized rank.
- **Cross-check.** `gk-l-gate-pos`'s natural tensor dual model of `EL_3(F_2[t])` also has
  `N_23 N_12 != 0` (artifact Section 4).
