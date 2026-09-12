---
rg: 2
id: period-four-kernel-excludes-omega-square-split
kind: route
title: Cancel both exterior sectors on a period-four core and descend to binary coefficients
target: two-sided-omega-square-deletion-candidate-has-no-split
requires: []
artifacts:
  - research/artifacts/kaplansky-two-sided-omega-square-period-four-kernel-2026-09-08.md
---

Write a=(0011)^infinity, b=(0110)^infinity, and
c=(1001)^infinity for actual binary tails. The full normalized
source

    X=(a+omega(b+c)) tensor b,
    Y=(omega a+b+c) tensor b

is nonzero and has zero image in both exterior target sectors
when z=omega^2. The artifact evaluates each natural block
explicitly, retaining the off-core tail 1b in the cancellation.

Since Y=omega X^sigma, multiplying by omega makes the source
Frobenius-fixed. Apply the established source transformation
tau D_z to obtain a nonzero binary vector w in im f_0 killed
by the actual T_z. If L T_z=f_0, applying the identity to w
would give 0=w, a contradiction. This excludes every possible
partner L for this candidate, beyond any finite support search.
