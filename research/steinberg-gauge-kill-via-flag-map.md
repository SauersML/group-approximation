---
rg: 2
id: steinberg-gauge-kill-via-flag-map
kind: route
title: Kill the Steinberg gauge by injectivity of the stacked flag-incidence map
target: authenticated-mixed-loop-kills-steinberg-gauges
requires:
  - steinberg-fox-kernel-is-flag-incidence
  - steinberg-flag-fox-map-is-injective
---

By `(SFI4)`, the common kernel of the two affine Fox rows on `St_p` is
exactly `ker D_p`.  The second prerequisite says that this kernel is zero
for every odd prime `p`, proving the target.
