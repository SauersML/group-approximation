---
rg: 2
id: leavitt-cone-half-pullback-route-to-nonhyperlinear
kind: route
title: St_20 of the binary Leavitt algebra is non-hyperlinear once pullbacks along the path-algebra surjection round on the Kazhdan cone half
target: non-hyperlinear-group
requires:
  - leavitt-st20-is-a-quotient-of-its-kazhdan-cone-half
  - leavitt-cone-half-pullback-rounding
---

**Route.**
- `leavitt-st20-is-a-quotient-of-its-kazhdan-cone-half`, item 5, says that `Delta = St_20(L_(F_2)(1,2))`
  is not hyperlinear iff `(PR)` holds.
- `leavitt-cone-half-pullback-rounding` is `(PR)`.
- `Delta` is a countable group (finitely generated, simple and infinite). So it witnesses
  `non-hyperlinear-group`.

**Relation to the amalgam route.** The route through
`leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding` needs `(QC)` and `(HR)`. This route
needs only `(PR)`, because the head bound for the quotient cover, `(QN)`, is proved. If `Delta_+`
is flexibly HS-stable, both `(HR)` and `(PR)` hold. On that hypothesis, the old route still needed
`(QC)`, and this one needs nothing more.
