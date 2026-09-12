---
rg: 2
id: index-three-corner-placement-identity-proof
kind: route
title: Two applications of the swap identity n_ij(r)n_jk(r') = n_jk(r')n_ij(r) + n_ik(rr')X_jk(r')X_ij(r)
target: index-three-corner-placement-holds-only-modulo-two-root-defects
requires: []
artifacts:
  - research/artifacts/rank-four-orthogonality-check-2026-09-12.md
---

Artifact `research/artifacts/rank-four-orthogonality-check-2026-09-12.md`, Sections 0 and 3.

**The swap identity.** The group identity `x_ij(r) x_jk(r') = x_ik(r r') x_jk(r') x_ij(r)`,
expanded after applying `sigma`, gives
`n_ij(r) n_jk(r') = n_jk(r') n_ij(r) + n_ik(r r') X_jk(r') X_ij(r)`. This uses no characteristic
assumption.

**The computation.**
1. Apply the identity to `n_43(1) n_31(b)`.
2. Commute `x_34(a)` past `x_31(b)`.
3. Apply the identity to `n_34(a) n_41(b)`.

**Honest values and the fourth index.**
- In an honest model both deviation products contain `E_31 E_34` or `E_41 E_34`, so they vanish.
- Replacing index 4 by 2 uses the identity at `(2,3,1)` and `(3,2,1)`, plus the commutation of
  `x_32` with `x_31`, all inside `EL_3`.

**Regular-representation example.**
- **Setup.** In `F_2[SL_8(F_2)]`, write `a = x_34(E_22)`, `b = x_43(1)`, `c = x_31(E_11)`,
  `d = x_13(1)`.
- **No sub-product is 1.** No nonempty ordered sub-product of `a, b, c, d` equals `1`. The
  candidates `ab`, `ac`, `bc`, `dc` are listed in Remark 3.1.
- **Conclusion.** So `(a - 1)(b - 1)(c - 1)(d - 1)` has coefficient `1` at the identity, and the
  cross term is nonzero.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 6.1 (identity, honest value and Remark 3.1 re-derived) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
