---
rg: 2
id: leavitt-nonhyperlinear-via-kun-thom-wreath-embedding
kind: route
title: Embed the Kun--Thom wreath in the unit group and inherit its nonhyperlinearity
target: leavitt-steinberg-hs-stable
requires:
  - kun-thom-wreath-embeds-in-leavitt-unit-group
  - theorem-e-vertex-rounds-to-unit-type-representations
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - kun-thom-wreath-carries-rigid-defect
  - leavitt-unit-hs-stable-iff-nonhyperlinear
artifacts:
  - research/artifacts/hyperlinear-nonsofic-l-times-2026-09-12.md
---

1. **The wreath is not hyperlinear.** The second, third and fourth prerequisites are exactly the
   prerequisites of `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding`. So the Kun--Thom
   coset wreath `W` is not hyperlinear.
2. **The unit group inherits this.** By the first prerequisite, `W` is a subgroup of
   `Q = L_(F_2)(1,2)^x`. Hyperlinearity passes to subgroups, so `Q` is not hyperlinear.
3. **Stability.** `leavitt-unit-hs-stable-iff-nonhyperlinear` gives `3 => 1`: `Q` is
   normalized-HS stable. Its identification `St_5(L) = Q` makes this `leavitt-steinberg-hs-stable`.

This is a live conditional. Its first and second prerequisites are open.
