---
rg: 2
id: artin-complexes-5333-and-533-11-by-cases
kind: route
title: Contractibility for [5,3,3,3] and [5,3,3^{1,1}] splits into the two diagrams separately
target: artin-complexes-of-5333-and-533-11-are-contractible
requires:
  - artin-complex-of-5-3-3-3-is-contractible
  - artin-complex-of-5-3-3-11-is-contractible
---

The target is the conjunction of the two requirements. The split separates the two diagrams
because they now need different inputs:

- `[5,3,3^{1,1}]` reduces to `h4-deligne-complex-upward-flag-toward-5-edge` through
  `artin-complex-5-3-3-11-contractible-via-b4-subdivision`;
- `[5,3,3,3]` has no reduction.
