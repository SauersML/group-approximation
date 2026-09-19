---
rg: 2
id: order-seven-compression-boundary-proof
kind: route
title: Prove the full-cut seventh-power telescope without identifying it with first-exit leakage
target: order-seven-anchor-stops-at-whitehead-compression-leakage
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - order-seven-first-exit-is-not-seven-step-leakage
---

For a contraction `T` and projection `E`, insert `E+(1-E)` successively
between the factors of `ET^7E`.  Contractivity gives

```text
||ET^7E-(ETE)^7||_2<=6||(1-E)TE||_2.                 (1)
```

If `ETE` is `zeta`-close to `M tensor D`, where `M^7=1` and `D^2=1`, the
ordinary power telescope gives

```text
||(ETE)^7-1 tensor D||_2<=7zeta.                     (2)
```

Combining `(1)--(2)` proves `(OSC1)--(OSC2)`.  This argument uses the full
cut boundary `||(1-E)TE||_2`.  The required first-exit fence records why the
separate operator `(OSC3)` only estimates `||(1-Q)TE||_2` for `E<=Q` and
cannot be substituted into `(1)`.  Thus the valid compression theorem and
the invalidated first-exit implementation are kept separate.
