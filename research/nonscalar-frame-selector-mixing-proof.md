---
rg: 2
id: nonscalar-frame-selector-mixing-proof
kind: route
title: Compress the frame inequality to the forbidden selector subspace
target: nonscalar-frame-or-selector-mixing-pays-forbidden-source
requires: []
---

Compress `(NSF4)` by the projection `F=Q(1-p)` and take normalized trace:

```text
kappa tr(F)
 <= sum_i tr(F S_i^*q_iS_i F)
  = sum_i ||q_iS_iF||_2^2.                              (NSP1)
```

Since `q_i<=p_i`, while `pF=0`, each summand satisfies

```text
q_iS_iF
 =q_ip_iS_iF
 =q_i(p_iS_i-S_ip)F.                                   (NSP2)
```

Left multiplication by a projection and right multiplication by `F` are
Hilbert--Schmidt contractions. Therefore

```text
||q_iS_iF||_2
 <=||(p_iS_i-S_ip)F||_2
 <=||p_iS_i-S_ip||_2.                                  (NSP3)
```

Summing the squares in `(NSP3)` and using
`tr(F)=||F||_2^2` proves `(NSF5)`.

If all selector intertwiners are exact, the right side is zero, so `(NSF5)`
gives `F=0`. Conversely, allowing non-equivariant transports creates no
unpriced loophole: every component of the frame that reaches `F` is bounded
by the corresponding literal selector-mixing residual in `(NSP2)`.

