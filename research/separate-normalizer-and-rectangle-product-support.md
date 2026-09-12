---
rg: 2
id: separate-normalizer-and-rectangle-product-support
kind: route
title: Separate the normalizer summand from every translated outside-normalizer rectangle term
target: rectangle-five-seven-retains-only-three-incidence-types
requires:
  - five-seven-partner-has-five-eulerian-incidence-types
  - z-fixed-support-five-hecke-normal-form
artifacts:
  - research/artifacts/five-seven-coefficient-and-adjoint-audit-2026-08-21.md
---

For `beta` supported in `N=N_G(H)`, the first product summand `h_0 beta`
lies in `F_2[N]`.  A term `a x c b`, with `a,c in H` and `b in N`, cannot
belong to `N`, since that would imply `x in N`.  Hence the rectangle summand
has support in the complement of `N`.  Equality to the identity separates
the summands and forces the impossible equality `h_0 beta=1`.  Removing the
two all-normalizer cycle partitions from the exhaustive five-type list
leaves the stated three.
