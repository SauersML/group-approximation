---
rg: 2
id: order-seven-compression-telescope-proof
kind: route
title: Telescope the seventh power across a nonreducing Hecke projection
target: order-seven-anchor-stops-at-whitehead-compression-leakage
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - native-whitehead-corner-collapses-hecke-flags
  - vanishing-loss-center-chain-authentication-hits-affine-firewall
---

For a contraction `T` and projection `E`, induction on `k` gives

```text
||ET^kE-(ETE)^k||_2
 <= (k-1)||(1-E)TE||_2.                               (1)
```

For the induction step, insert `E+(1-E)` between `T^k` and `T`; the old
difference is multiplied by a contraction and the new crossing is bounded
by `||(1-E)TE||_2`.  Taking `k=7` and using `T=Jv` proves `(OSC1)` without
assuming that `E` reduce either factor.

If `C=ETE` and `C_0=M tensor D` with `||C-C_0||_2<=zeta`, the ordinary
power telescope gives `||C^7-C_0^7||_2<=7zeta`.  The order-seven packet
calculation gives `C_0^7=1 tensor D`, so the triangle inequality with
`(OSC1)` proves `(OSC2)`.

For `(OSC4)`, take the low spectral projection `E_n` of the positive sum
`(OSC3)`.  Its complement has the asserted trace, and

```text
||(1-Q_n)J_(i,n)v_(i,n)E_n||_2^2
 =tau_n(E_n v_(i,n)^*J_(i,n)(1-Q_n)J_(i,n)v_(i,n)E_n)
```

is bounded by the spectral threshold.  This controls the exit from `Q_n`,
not the exit from `E_n`, so it cannot be inserted into `(1)` with `E=E_n`
without a separate boundary theorem.  The exact counterexample in
`order-seven-first-exit-is-not-seven-step-leakage` shows this distinction is
sharp.  The established regular-model calculation independently shows why
no zero-defect tracial estimate can supply even this first-exit spectral
bound.
