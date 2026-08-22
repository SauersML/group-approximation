---
rg: 2
id: regular-inner-adjoint-literature-boundary-proof
kind: route
title: Intersect the primary stability theorems with the canonical inner-adjoint quantifiers
target: sl3-rigidity-stops-before-inner-adjoint-correction
requires:
  - infinite-hyperlinear-kazhdan-group-is-not-hs-stable
  - character-rigidity-equals-hyperfinite-hs-stability
  - sl3-regular-projective-correction-is-inner-adjoint-stability
---

The two negative primary theorems quantify over all approximate
homomorphisms and conclude existence of at least one noncorrectable
challenge.  They do not impose the conjunction of regular trace, adjoint
form, and projective-inner correction, so they cannot refute the restricted
condition.

The positive Dogon--Vigdorovich theorem has the opposite scope restriction:
it corrects sequences with hyperfinite limiting trace.  The regular
character generates `L(SL_3(Z))`.  Since `SL_3(Z)` is nonamenable, its group
factor is nonamenable, while every finite hyperfinite von Neumann algebra is
amenable.  Hence the regular sequence is outside the theorem's hypothesis.

The exact calculation in
`sl3-regular-projective-correction-is-inner-adjoint-stability` shows that
the missing projective assertion is neither repaired by passing to the
adjoint tuple nor by applying arbitrary HS correction there: the corrected
representation must stay inner.  Comparing these quantifiers proves the
stated literature boundary.
