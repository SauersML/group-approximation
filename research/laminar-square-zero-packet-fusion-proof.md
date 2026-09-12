---
rg: 2
id: laminar-square-zero-packet-fusion-proof
kind: route
title: Add one nilpotent from each orthogonal maximal packet ideal
target: laminar-square-zero-packets-fuse-intrinsically
requires: []
artifacts:
  - research/artifacts/stw99-lxxiii-lxvi-focused-audit-2026-08-31.md
---

Discard every packet ideal contained in another packet ideal, and retain one
generator `x_j` for each distinct maximal ideal `I_j`.  Distinct retained
ideals are incomparable.  The laminar hypothesis therefore makes their
intersections zero, hence `I_j I_k=0` for `j!=k`.

For `x=sum_j x_j`, all mixed products vanish and `x^2=0`.  Moreover

```text
x*x=sum_j x_j*x_j,
Ideal(x)=Ideal(x*x)=sum_j Ideal(x_j*x_j)=sum_j I_j.
```

Every discarded ideal lies in a retained maximal ideal, so the last sum is
the ideal sum of the original packet.
