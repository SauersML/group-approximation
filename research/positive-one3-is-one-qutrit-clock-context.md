---
rg: 2
id: positive-one3-is-one-qutrit-clock-context
kind: claim
title: One order-three clock is exactly the local positive-ONE3 context algebra
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  central-tagged-one-in-three-is-a-finite-lcs-or: that fixes one Boolean coordinate and decomposes into binary affine sectors; this identifies the entire three-atom context with one qutrit clock without choosing a Boolean branch.
  one-hot-selector-parity-barrier: that rules out binary affine enforcement of three one-hot atoms; this changes coefficient field and records the exact local C-star-algebra isomorphism, leaving only cross-context projector equality.
---

Let `omega=exp(2 pi i/3)` and let `T` be an order-three unitary with spectral
projections `E_0,E_1,E_2` for eigenvalues `1,omega,omega^2`.  Put

```text
U_x=T,             U_y=omega^(-1)T,             U_z=omega T.
```

Then

```text
Pi_0(U_x)=E_0,       Pi_0(U_y)=E_1,       Pi_0(U_z)=E_2,
E_0+E_1+E_2=1.                                          (QOC1)
```

Hence the three Boolean truth projections have exactly the positive-ONE3
support `100,010,001`, and the local constraint algebra `C^3` is exactly
`C[Z_3]`.

With a central order-three element `J` represented by `omega`, the clause
uses only

```text
U_y=J^(-1)U_x,              U_z=J U_x.                  (QOC2)
```

If a Boolean variable occurs in positions `a,b in Z_3` of clause clocks
`T_c,T_d`, its consistency relation is precisely

```text
Pi_0(J^(-a)T_c)=Pi_0(J^(-b)T_d).                        (QOC3)
```

Thus no nonlinear local clause remains; `(QOC3)` is the sole new
groupification interface.

