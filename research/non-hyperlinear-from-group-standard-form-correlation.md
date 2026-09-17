---
rg: 2
id: non-hyperlinear-from-group-standard-form-correlation
kind: route
title: A finite correlation outside C_qa realized in the standard form of a group von Neumann algebra certifies non-hyperlinearity
target: non-hyperlinear-group
requires:
  - ce-standard-form-strategies-are-quantum-approximable
  - explicit-group-standard-form-correlation-outside-qa
---

Let `Lambda`, the measurements and `xi` be as in
`explicit-group-standard-form-correlation-outside-qa`. If `Lambda` were
hyperlinear, `L(Lambda)` with its canonical trace would be Connes
embeddable. Then `ce-standard-form-strategies-are-quantum-approximable`
would place the correlation in `C_qa`, a contradiction. Hence `Lambda` is a
finitely presented non-hyperlinear group.

The route is a decomposition of the assignment "a group whose
hyperlinearity would make the game value approximable" into three parts:
- an established transfer inequality: the value of every Bell functional on a standard-form strategy over `L(Lambda)` is at most its `C_qa` supremum when `Lambda` is hyperlinear;
- an available game-side separation (`lin-pzk-tableau-rational-qc-not-qa-correlation`);
- one open host-side realization.

For perfect synchronous witnesses the host-side step collapses to the corner
model problem (`standard-form-group-separation-collapses-to-corner-model`).
Only non-synchronous or imperfect witnesses give this route room beyond
`non-hyperlinear-from-group-factor-bcs-model`.
