---
rg: 2
id: mf-radical-sandwiched-by-hilbert-hotel-radical
kind: claim
title: The MF radical of an elementary group is sandwiched between the relative elementary and congruence subgroups of the Hilbert-hotel radical
distinct_from:
  purely-infinite-unit-group-max-mf-quotient-is-k1: that computes the general linear MF quotient for purely infinite simple rings, the single case where the Hilbert-hotel radical is the unit ideal; this bounds the elementary MF radical for every torsion ring and names the relative K_1 group that measures the remaining slack.
  kazhdan-elementary-approximation-type-mirrors-ring-type: that is the three-rung ladder of equivalences for simple rings, where the Hilbert-hotel radical takes only the values 0 and R; this drops simplicity and asks for the value of the radical rather than which side of a dichotomy holds.
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

**ESTABLISHED** (route `mf-radical-sandwiched-by-hilbert-hotel-proof`, artifact section 5).

Let `R` be a countable unital ring with torsion additive group, `n >= 4`, and `hh = hh(R)` the
Hilbert-hotel radical. If `EL_n(R/hh)` is MF, then

```text
EL_n(R, hh)  <=  Rad_MF(EL_n(R))  <=  EL_n(R) n GL_n(R, hh),
```

so the maximal MF quotient of `EL_n(R)` lies between `EL_n(R/hh)` and `EL_n(R)/EL_n(R,hh)`.
The two ends agree exactly when the relative group `(EL_n(R) n GL_n(R,hh)) / EL_n(R,hh)` vanishes,
and then `Rad_MF(EL_n(R)) = EL_n(R,hh)` with maximal MF quotient `EL_n(R/hh)`.

This is where the two calibrating results meet. The **paradox side supplies the radical**, through
one-sided Kazhdan transport; the **measure side supplies the hypothesis** that `EL_n(R/hh)` is MF,
through LEF towers, residually finite actions or exact matricial models; and the meeting point is the
single ideal `hh(R)`. The residual slack is a relative `K_1` group, the same correction term that
appears in `thm:mf-quotient-units` of the manuscript.

Model tests, in artifact section 6: `hh = R` for simple rings that are not directly finite, which
recovers `cor:simple-infinite-ring`; `hh = 0` for the Pestov 9.1 ring, where the statement reduces
to the tautology that the radical is trivial iff the group is MF; `hh = JeJ` for the
Toeplitz-Jacobson algebra, where the manuscript proves the equality directly and the maximal MF
quotient is `EL_n(F_2[z,z^-1])`.
