---
rg: 2
id: leavitt-unit-hyperlinear-from-steinberg-instability
kind: route
title: An unstable Steinberg cover makes the binary Leavitt unit group hyperlinear
target: binary-leavitt-unit-group-hyperlinear
requires:
  - leavitt-steinberg-hs-unstable
  - steinberg-hs-stability-equals-nonhyperlinearity
  - leavitt-gl-equals-el-and-perfect-unit-group
---

If `U = St_5(L_(F_2)(1,2))` is not normalized-HS stable, condition 3 of
`steinberg-hs-stability-equals-nonhyperlinearity` fails, so `Q = EL_4(L)` is
hyperlinear. By `leavitt-gl-equals-el-and-perfect-unit-group`, `GL_4(L) = EL_4(L)`,
and the four-leaf prefix code gives `M_4(L) ~= L` as unital rings. Hence
`Q ~= GL_4(L) ~= L^x`, and `L^x` is hyperlinear.

After `leavitt-steinberg-map-iso-from-rank-three` (Khanh, arXiv:2609.08428v1,
Theorem 5.4), `U ~= GL_5(L) ~= L^x` as well. So no central quotient
intervenes: the Steinberg cover, `Q` and the unit group are one simple group,
and the "phrasing trap" of the equivalence node (nonhyperlinearity of `Q`
versus of `U`) is empty for this ring.

**Cycle, on purpose.** This route and
`steinberg-instability-from-leavitt-unit-hyperlinear` record one equivalence:
the unstable Steinberg branch is the binary Leavitt hyperlinearity question.
`check` warns about the cycle. A least fixpoint never fires a cycle, so
neither claim establishes itself, and neither route should be deleted as
redundant.
