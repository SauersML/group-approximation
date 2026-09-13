---
rg: 2
id: summand-no-weakly-finite-image-from-no-representation
kind: route
title: A weakly finite image of the anti-central summand is a nontrivial weakly finite representation
target: ternary-anti-central-summand-has-no-weakly-finite-image
requires:
  - ternary-leavitt-units-have-no-weakly-finite-representation
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

Take a nonzero weakly finite quotient `W` of `S_-`. The group `G` maps into `W^x` with `z -> -1`, which is not
`1` because `2` is invertible and `W != 0`. So `W` carries a nontrivial weakly finite representation. Given the
required claim, no such `W` exists.

This route forms an intended cycle with `no-weakly-finite-representation-from-summand-obstruction`.
