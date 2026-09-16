---
rg: 2
id: non-type-f-non-proper-bnsr-by-virtual-cd-dichotomy
kind: route
title: "Non-proper BNSR inclusion for F_infinity groups without a finite classifying space: split by whether some finite-index subgroup has finite cohomological dimension"
target: non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion
requires:
  - virtually-finite-cd-f-infinity-groups-have-stable-bnsr
  - f-infinity-without-finite-vcd-non-proper-bnsr-inclusion
---

Let `G` be a group of type `F_∞` with no finite classifying space. Either some
subgroup of finite index in `G` has finite cohomological dimension, or none
does.

- **Some finite-index subgroup `H` has `cd H = d < ∞`.** By
  `virtually-finite-cd-f-infinity-groups-have-stable-bnsr`,
  `Σ^e(G) = Σ^{e+1}(G)` with `e = max(d,2)`.
- **No finite-index subgroup has finite cohomological dimension.** By
  `f-infinity-without-finite-vcd-non-proper-bnsr-inclusion`, some `m ≥ 1` has
  `Σ^m(G) = Σ^{m+1}(G)`.

The two cases are exhaustive, so the prerequisites give the target. The
hypothesis "no finite classifying space" is not used. The first prerequisite
is established. The open content is the second, which is a smaller class:

- it excludes every group of type VF, for example every elementary amenable
  group of type `F_∞` (`elementary-amenable-f-infinity-groups-are-type-vf`);
- it excludes every hypothetical group of type `F_∞` with finite cohomological
  dimension that is not of type F.
