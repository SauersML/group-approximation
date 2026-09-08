---
rg: 2
id: leavitt-uniform-gap-via-tracial-moment-certificate
kind: route
title: Dead. Certify the 24k uniform gap by a finite tracial moment relaxation
target: leavitt-24k-feasibility-has-a-uniform-gap
requires: []
artifacts:
  - research/artifacts/leavitt-tracial-moment-relaxation-no-go-2026-09-08.md
---

**DEAD.**  Invalidated by
`tracial-moment-relaxations-cannot-certify-the-leavitt-gap`.

## The attempt

The target asks for `m` and `eta > 0` bounding
`max_(r in T_m) ||pi_(k,U)(r) - I||_(2,24k)` below, uniformly in `k` and
`U`.  That is a tracial optimization over unitary tuples, and the standard
way to lower-bound such a quantity without constructing the optimum is a
moment relaxation: keep finitely many variables `y_w`, impose moment-matrix
positivity, the unitary word identities, traciality, the true relations of
`H` that fit at that level, and the prescribed regular characters on the
two frozen finite factors; then read a positive optimum, or a
sum-of-squares certificate for one, as the required `eta`.  It is
attractive here because the criterion already freezes both finite factors,
so the relaxation starts with unusually strong prescribed data.

## Why it dies

`tracial-moment-relaxations-cannot-certify-the-leavitt-gap` proves that
`y_w = 1_(q(w)=1)` is feasible at every finite level and makes the defect
energy exactly zero, so **every** level has optimum zero, no matter how
many true relations or canonical moments are adjoined.  The group-algebra
trace `tau` gives the certificate form of the same fact: any derivation
using only positivity, traciality, the group relations and the character
values is sound for `tau`, where every relator defect vanishes.

So the failure is not a matter of going to a higher level, nor of
strengthening the prescribed data; it is that the premises of this family
of certificates are all true of an object that has no gap.  A proof of the
target must use something the relaxation does not see — a genuine
finite-dimensionality input, which is exactly what
`leavitt-24k-models-avoid-blockwise-error-basis-normalizers` uses inside
its restricted model class.
