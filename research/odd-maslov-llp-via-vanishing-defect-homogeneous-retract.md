---
rg: 2
id: odd-maslov-llp-via-vanishing-defect-homogeneous-retract
kind: route
title: Scalarize a homogeneous odd-to-even retract by driving its coefficient boundary to zero
target: sp4-mod3-twisted-fibres-have-llp
requires:
  - odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap
---

**INVALIDATED.**  The proposed route was to construct homogeneous split ucp
maps from an odd Maslov fibre into matrix amplifications of an even fibre,
let the coefficient size grow, and make the two-sided multiplicative defects
of the coefficient functions tend to zero.  One would then perturb the
coefficients toward a scalar or finite projective Morita bridge and pull LLP
back from the even fibre.

`odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap` proves that
the sum of those normalized coefficient defects is at least one constant
`kappa_hom>0`, independently of matrix size.  Thus no such vanishing-boundary
sequence exists.  Any surviving homogeneous retract proof must instead use
a genuinely nonfaithful left inverse which kills a macroscopic positive
boundary; it cannot reach LLP by asymptotic scalarization.
