---
rg: 2
id: relative-congruence-exactification-closes-outlier
kind: route
title: Flexibly exactify the regular pair into congruence packets and apply uniform repair
target: iwahori-outlier-repair
requires:
  - regular-iwahori-relative-congruence-exactification
  - mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding
  - odd-label-stabilization-has-uniform-repair
---

Apply `(RCE1)--(RCE2)` to a sequence in the central-regular outlier
sector on dimensions `d_n`. The result is a congruence vertex pair on
common dimensions

```text
D_n>=d_n,       D_n/d_n->1,
```

at generalized distance `o(1)` from the input and with defect `o(1)`.
The mixed-CRT reduction and uniform odd-label theorem replace that pair,
in the same enlarged dimension `D_n` and at normalized-HS cost `o(1)`, by
a literally compatible pair. Composing the two perturbations gives a
flexible repair of the original pair. Its exact edge intertwiner has full
rank `D_n`; relative to the original coordinates, the comparison is
almost full and uses only `D_n-d_n=o(d_n)` boundary dimensions. This is
the rank allowance in `iwahori-outlier-repair`.

The flexible qualification is necessary, not cosmetic.
`regular-iwahori-strict-congruence-exactification-is-false` gives exact
regular SL2 vertex pairs for which every same-dimensional exact endpoint
stays uniformly far away, while one added line repairs the pair. Thus this
route cannot promise a full-rank intertwiner in the original dimension.

This route explains the exact dependency after congruence closure. The
congruence repair theorem is the second step, not the first: it cannot be
applied directly to the localized high-dimensional edge types because
`modular-vertex-extension-does-not-force-congruence` shows that their vertex
extensions may have infinite image.
