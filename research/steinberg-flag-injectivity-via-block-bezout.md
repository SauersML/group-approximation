---
rg: 2
id: steinberg-flag-injectivity-via-block-bezout
kind: route
title: Close Steinberg flag injectivity by a unit-ideal certificate in the defect-zero block
target: steinberg-flag-fox-map-is-injective
requires:
  - steinberg-fox-injectivity-is-block-bezout
  - steinberg-fox-rows-generate-defect-zero-block
---

Apply `(SBUG1)` to a vector killed by both Fox rows.  The block Bezout
identity sends that vector to itself, so it is zero.  The established
equivalence then identifies this common-kernel statement with injectivity of
the authenticated flag-incidence map `D_p`.
