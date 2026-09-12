---
rg: 2
id: natural-leavitt-pair-lifts-partial-symmetry-proof
kind: route
title: Compute the Gram defect grade by grade in the odd-measure crossed product
target: natural-leavitt-pair-lifts-have-partial-symmetry-defect
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-cohn-mixed-depth-lifts-2026-09-12.md
  - research/artifacts/gk-vf-linear-b-verification-2026-09-12.md
---

Section 2 of the artifact, Lemma 2.1.
- The identity grade of `tau sigma` is `P_0 + P_1 = 1`, because `g_0^-1(00) = 0` and `g_1^-1(01) = 1`.
- The two cross grades are `[h]1_(W_1)` and `[h^-1]1_(W_2)`.
- `W_1 ⊆ U_1` and `W_2 ⊆ U_0` are disjoint, and neither contains a Dirac measure.
- `h(A) = 0` and `h(1) = B'` give `h W_1 = W_2`.
- `h^-1 W_1 ∩ W_1 = ∅` and `h W_2 ∩ W_2 = ∅` follow from total mass one: a measure there would have
  `mu(0) = mu(1) = 1`.
- Hence `D^2 = F`, `DF = FD = D`, and `(F ± D)^2 = 2(F ± D)` in characteristic three.
- The correction `c = (1 - F) + 2e = 1 + D`, where `e = 2(F + D)`, satisfies `c tau sigma = c^2 = 1 - e'`.

*Verification by `w3-vf-linear` (2026-09-12), Section 5.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed: the grades, h != 1, h(A) = 0, h(1) = B', h^-1(1) = 1 ∪ (0\A), h(0) = 0 ∪ (1\B'), the eight products, and c = 1 + D = tau sigma with c^2 = 1 - e'. The Remark 2.3 matrix units check.*

**Correction (w4-vf-linear-b, 2026-09-12).** An earlier version of the last bullet displayed
`c = (1 - F) + 2(F + D)`. That element equals `1 - e'`, and multiplying it onto `tau sigma` gives
`tau sigma = 1 + D`, not `1 - e'`. The correct factor is `c = (1 - F) + 2e = 1 + D`, as in the artifact's
Lemma 2.1 item 5 and in the verification above. No conclusion changes
(`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, Section 1).
