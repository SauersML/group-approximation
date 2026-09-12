---
rg: 2
id: non-rf-hyperbolic-from-non-mf-hyperbolic
kind: route
title: A non-MF hyperbolic group is not residually finite
target: non-residually-finite-hyperbolic-group
requires:
  - non-mf-hyperbolic-group
  - mf-positive-controls
---

Countable residually finite groups are MF (`mf-positive-controls`), and a
hyperbolic group is finitely generated, hence countable.  So a non-MF
hyperbolic group is not residually finite.

With `quotientless-hyperbolic-via-kapovich-wise`,
`kazhdan-quotientless-hyperbolic-via-common-quotient` and
`non-mf-hyperbolic-from-kazhdan-quotientless` this closes the intended cycle
recorded by `hyperbolic-rf-question-equals-non-mf-question`.
