---
rg: 2
id: exactly-matricial-rings-have-lef-general-linear-groups
kind: claim
title: A ring embedding unitally in an algebraic ultraproduct of matrix algebras over arbitrary fields has LEF general linear groups
distinct_from:
  stably-mf-elementary-groups-force-matricial-rings: that is the open converse, asking whether stably MF or LEF elementary groups force exact matricial embeddability; this is the proved direction
  mf-elementary-groups-force-stably-finite-simple-rings: that is the necessary condition, stable finiteness, from the paradox side; this is the sufficient condition, exact matricial embeddability, from the measure side
artifacts:
  - research/artifacts/un-converse-stable-finiteness-boundary-2026-09-13.md
---

**ESTABLISHED** (route `exactly-matricial-rings-have-lef-general-linear-groups-proof`; artifact §4). Unreviewed.
Standard inputs, recalled rather than imported: Łoś's theorem for ultraproducts, Malcev's theorem (finitely
generated linear groups over commutative fields are residually finite), Elek–Szabó (LEF ⇒ sofic).

Let `R` be a countable unital ring with an injective unital ring homomorphism `R → ∏_ω M_(d_k)(F_k)`, where the
`F_k` are arbitrary commutative fields. Then for every `N >= 1`, `GL_N(R)` is LEF. So every subgroup of it,
including `EL_N(R)`, is LEF, and hence sofic, hyperlinear and MF.

Instances:
- **The Pestov ring** `LC(X, F_q) ⋊ Z`, with `F_k = F_q`. This is step 3.3 of
  `research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`.
- **`M_d(F)`.**
- **The Weyl algebra** `A_1(Q)`, via characteristic-p towers (`weyl-algebra-is-exactly-matricial`).

Malcev is what removes the restriction to finite fields: the coordinate groups `GL_(N d_k)(F_k)` may be infinite,
and residual finiteness of the finitely generated subgroup they generate supplies finite images.

**Review (un-verify-3, 2026-09-13): PASS.** Re-derived: units of the ultraproduct are coordinatewise units, Łoś on a finite window, Malcev for the finitely generated linear image, and LEF ⟹ MF through regular permutation unitaries with `‖V_n(g) − 1‖ ≥ √2`. No conflicting node (e.g. `cohn-elementary-group-is-not-lef` concerns a ring that is not directly finite). `research/artifacts/un-review3-2026-09-13-part1.md` §6.
