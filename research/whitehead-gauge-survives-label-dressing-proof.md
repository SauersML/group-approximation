---
rg: 2
id: whitehead-gauge-survives-label-dressing-proof
kind: route
title: Multiply the packet tensor factors and use unitary invariance of normalized Hilbert--Schmidt norm
target: label-only-dressing-cannot-ungauge-a-whitehead-bridge
requires: []
---

Tensor multiplication gives

```text
(P_s tensor 1)(M_J tensor D)(N_r tensor 1)
  =(P_s M_J N_r) tensor D.                                (1)
```

Induction proves the same formula for any finite alternating list of
label-only source and range dressings surrounding the single gauged
occurrence.  If `N=P_sM_JN_r` is the required label transport, normalized
Hilbert--Schmidt tensor factorization and unitarity of `N` give

```text
||N tensor D-N tensor 1||_2
 =||N tensor (D-1)||_2
 =||D-1||_2.                                             (2)
```

For approximate typings, replace the factors one at a time.  Multiplication
by contractions does not increase normalized Hilbert--Schmidt norm, so the
difference from `(1)` is at most the sum of all chart errors.  Applying the
triangle inequality to `(2)` gives the asserted asymptotic version.
