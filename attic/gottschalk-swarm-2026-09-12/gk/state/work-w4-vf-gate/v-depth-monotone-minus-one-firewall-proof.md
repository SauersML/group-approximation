---
rg: 2
id: depth-monotone-minus-one-firewall-proof
kind: route
title: Extend the stably finite embedding linearly to the group algebra and read off the reflection ideal
target: depth-monotone-configurations-cannot-force-ternary-minus-one
requires:
  - depth-monotone-leavitt-subalgebras-are-stably-finite
artifacts:
  - research/artifacts/depth-monotone-leavitt-firewall-2026-09-12.md
---
Artifact Section 3. **OPEN** until `w4-vf-gate` passes it.
1. **Model.** Conjugate the subgroup into a weighted unit group. The embedding of
   `depth-monotone-leavitt-subalgebras-are-stably-finite` extends to a unital ring map `F_3[Γ_0] -> Q`, or into
   `Q^op` on the opposite side, with `[z] -> -1` and `ε_- -> 1`.
2. **Reflection ideal.** Theorem 1(b) of
   `research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md` kills `J_omega`,
   while `1 -> 1`. A certificate confined to `Γ_0` is a derivation inside `ε_- F_3[Γ_0]`.
3. **Placement.** Degrees of `T_(0,1)`, `T_(1,00)`, level `V`, `E` and the level roots are nonpositive for the
   standard grading. The Kraft lemma and the depth-vector table (Section 4) record what escapes.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 30.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
