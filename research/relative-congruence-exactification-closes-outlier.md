---
rg: 2
id: relative-congruence-exactification-closes-outlier
kind: route
title: Exactify the regular pair into congruence packets and apply uniform repair
target: iwahori-outlier-repair
requires:
  - regular-iwahori-relative-congruence-exactification
  - mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding
  - odd-label-stabilization-has-uniform-repair
---

Apply `(RCE1)--(RCE2)` to a sequence in the central-regular outlier sector.
The resulting congruence vertex pair has defect `o(1)`.  The mixed-CRT
reduction and uniform odd-label theorem replace it, in the same dimension
and at normalized-HS cost `o(1)`, by a literally compatible pair.  Composing
the two perturbations repairs the original pair and
provides the full-rank exact edge intertwiner required by
`iwahori-outlier-repair`.

This route explains the exact dependency after congruence closure.  The
congruence repair theorem is the second step, not the first: it cannot be
applied directly to the localized high-dimensional edge types because
`modular-vertex-extension-does-not-force-congruence` shows that their vertex
extensions may have infinite image.
