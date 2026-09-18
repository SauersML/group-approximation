---
rg: 2
id: titz-witzel-flat-hitting-via-soficity-and-2d-vtf
kind: route
title: Soficity of the Titz--Witzel kernel plus virtual torsion-freeness of 2-dimensional CAT(0) hyperbolic groups gives the flat-hitting covers
target: titz-witzel-flat-hitting-sparse-branched-covers
requires:
  - titz-witzel-kernel-sofic
  - two-dimensional-cat0-hyperbolic-groups-virtually-torsion-free
  - sofic-lattice-plus-hyperbolic-vtf-gives-flat-hitting-covers
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Apply `sofic-lattice-plus-hyperbolic-vtf-gives-flat-hitting-covers` to
`Y = Y_1^2` with girths 10 at `v, w` and 6 at the `u_i`. Its hypotheses check
out as follows.
* The closed cells of `Y` embed: each triangle has one vertex of each of the
  three types.
* The links (the `GQ(2,2)` incidence graph and `K_(3,3)`) contain cycles.
* `10 · π/4 > 2π` and `6 · π/2 > 2π`.
* (S): `K = Gamma_1^2` has finite index in `pi_1(Y_1^2)`, by
  `titz-witzel-simple-kazhdan-cat0-lattices-exist`, and is sofic by
  `titz-witzel-kernel-sofic`.
* (V2) is `two-dimensional-cat0-hyperbolic-groups-virtually-torsion-free`.

The conclusion is conditions 1–3 of the target. Condition (H) is in its
"lifted from any vertex" form.

**The squeeze.** `titz-witzel-kernel-sofic-via-connected-link-covers` has the
target as its only open prerequisite. So under (V2),

```text
titz-witzel-flat-hitting-sparse-branched-covers  <=>  titz-witzel-kernel-sofic .
```

Unconditionally, refuting the target while `K` is sofic produces a
2-dimensional CAT(0) hyperbolic group that is not virtually torsion-free. That
group is then also not residually finite, by
`hyperbolic-rf-question-equals-vtf-question`.
