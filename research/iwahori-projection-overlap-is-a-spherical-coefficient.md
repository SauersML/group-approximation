---
rg: 2
id: iwahori-projection-overlap-is-a-spherical-coefficient
kind: claim
title: One Iwahori projection-transfer defect is exactly one centered spherical coefficient dent
artifacts:
  - research/artifacts/canonical-iwahori-one-overlap-audit-2026-08-21.md
distinct_from:
  iwahori-transfer-failure-has-two-positive-density-blocks: that bounds the physical ranks from a failed commutator; this identifies the exact normalized positive-definite coefficient carried by that projection.
  projective-trace-square-transfer-for-sl3-pair: that asks for a trace-square inequality for subgroup-central unitaries in the higher-rank pair; this is a mixed projection-compression identity for the rank-one Iwahori pair.
---

Let `rho:A->U(calM)` be a tracial representation of the Iwahori amalgam,
let `P` be a projection commuting with `rho(C_+)`, and put

```text
t=tau(P),       Z=P-t1,       U=rho(g),
alpha_g=tau(P U P U^*).                                      (IOS1)
```

For `0<t<1`, the function

```text
phi_P(g)=<Z,Ad_(rho(g))(Z)>_2 / (t(1-t))
        =(alpha_g-t^2)/(t(1-t))                              (IOS2)
```

is a normalized positive-definite `C_+`-bi-invariant function on `A`.
Moreover

```text
||[P,U]||_2^2=2(t-alpha_g),
1-phi_P(g)=||[P,U]||_2^2/(2t(1-t)).                          (IOS3)
```

Thus a positive-density failed transfer with commutator at least `epsilon`
produces one spherical coefficient satisfying

```text
phi_P(g) <= 1-2 epsilon^2,                                   (IOS4)
```

because `t(1-t)<=1/4`.  Conversely coefficient convergence to one for the
fixed second-vertex generators is exactly projection commutant transfer.
