---
rg: 2
id: arithmetic-defect-core-via-sofic-saturation
kind: route
title: Use the arithmetic saturated quotient as the split-Z radical kernel
target: torsion-free-sofic-singly-generated-kazhdan-defect-core
requires:
  - arithmetic-defect-saturated-kazhdan-group-is-sofic
  - arithmetic-single-defect-saturation
  - defect-saturation-full-mf-radical
  - concrete-compression-source
  - affine-congruence-source-is-kazhdan
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
  - research/artifacts/torsion-free-full-mf-radical-2026-08-19.md
---

Take the arithmetic quotient `Q` from `(ADS1)`.  The audited routing theorem
already makes it finitely presented, torsion-free and property `(T)`;
`arithmetic-defect-saturated-kazhdan-group-is-sofic` adds the only missing
positive property.  The image of the affine Kazhdan source supplies `L`, and
the saturation identity gives

```text
D_Q(L)=Q=<<q(sigma)>>^Q.
```

Thus `K=Q` and `k=q(sigma)` satisfy every clause of `(TFC1)`.

