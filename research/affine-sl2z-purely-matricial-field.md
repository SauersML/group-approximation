---
rg: 2
id: affine-sl2z-purely-matricial-field
kind: claim
title: Z^2 x| SL_2(Z) is purely matricial field, so relative property (T) does not obstruct strong convergence
---

ESTABLISHED (unreviewed as a reading; the theorem is Gao--Kunnawalkam
Elayavalli--Mj's).  The affine group `Z^2 x| SL_2(Z)` has finite-dimensional
unitary representations with finite image that converge strongly to its
regular representation.  The same holds for the integral maximal parabolics
`Z^2 x| GL_2(Z)` of `SL_3(Z)`.

Why it matters here.  `(Z^2 x| SL_2(Z), Z^2)` has relative property (T), so the
group is not a-T-menable.  Every class of PMF groups listed by Magee--de la
Salle (arXiv:2312.03220v2, p. 2) and by van Handel's survey (arXiv:2510.12520,
Section 2.3) is a-T-menable, and Magee--de la Salle write "as far as we know
there is no direct relation" between property (T) and PMF.  This claim shows
that relative property (T) for an infinite normal subgroup is compatible with
PMF.  For `sl3z-purely-matricial-field` it says two things:

- a refutation cannot live in one maximal parabolic of `SL_3(Z)`;
- a refutation cannot rest on relative property (T) alone.

What stays untested is full property (T) of an infinite group
(`infinite-kazhdan-group-with-mf-reduced-cstar`).

Proof: `affine-sl2z-purely-matricial-field-proof`.
