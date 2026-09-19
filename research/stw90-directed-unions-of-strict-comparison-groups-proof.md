---
rg: 2
id: stw90-directed-unions-of-strict-comparison-groups-proof
kind: route
title: Use reduced-norm subgroup inclusions and the cutdown permanence theorem
target: stw90-directed-unions-of-strict-comparison-groups
requires:
  - directed-unions-preserve-tracial-strict-comparison
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

For `H<=G`, restriction of `lambda_G` to `H` is an amplification of
`lambda_H` over the left cosets of `H`.  Thus `C*_r(H)` embeds unitally and
isometrically into `C*_r(G)`, and the canonical traces agree on it.  The
directed union of the images `C*_r(G_i)` contains `C[G]` and is norm dense in
`C*_r(G)`.  The general directed-union strict-comparison theorem therefore
gives the first assertion.

For the simplicity assertion, put `A=C*_r(G)` and suppose all
`A_i=C*_r(G_i)` are simple.  If `J` is a nonzero ideal of `A`, take
`0 != a in J_+` and approximate it closely by `b in (A_i)_+`.  With the
approximation smaller than one quarter of `||a||`, a nonzero cutdown
`c=(b-eta)_+` satisfies `c <=_Cu a`.  Hence `c` belongs to the ideal generated
by `a`, so `0 != c in J cap A_i`.  This intersection is an ideal of the simple
unital algebra `A_i`, and therefore contains its unit.  The inclusions are
unital, so `1_A in J` and `J=A`.

**Trust boundary.**  Reduced-norm injectivity, trace compatibility, density,
and simplicity are proved directly.  The only prerequisite is the preceding
quantitative directed-union comparison theorem.
