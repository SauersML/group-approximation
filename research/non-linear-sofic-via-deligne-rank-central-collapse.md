---
rg: 2
id: non-linear-sofic-via-deligne-rank-central-collapse
kind: route
title: If every characteristic-p rank model of Deligne's triple cover kills its central mark, the cover is not F_p-linear sofic
target: non-linear-sofic-group
requires:
  - deligne-central-mark-dies-in-char-p-rank-models
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Artifact Section 3.0 and Corollary 3.5.
- **Models to homomorphisms.** A linear sofic approximation of `E_3` over `F_p`, with separation `delta` on `z`,
  would give in an ultraproduct a homomorphism into a rank ultraproduct unit group with `rk(psi(z) - 1) >= delta`.
  Extending scalars from `F_p` to an algebraic closure keeps normalized rank.
- **Conclusion.** If `z` is in `Rad_rk,p(E_3)`, no such approximation exists, so `E_3` is not `F_p`-linear sofic.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 25.5 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. Checked:*
- *models give ultraproduct homomorphisms separating `z` after extending scalars;*
- *`Rad_rk,p(E_3) ⊆ ⟨z⟩` through the residually finite quotient;*
- *`rank(ψ(z)^2 - 1) = rank(ψ(z) - 1)` for an element of order 3.*
