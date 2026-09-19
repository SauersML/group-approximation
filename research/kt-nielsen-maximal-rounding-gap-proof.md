---
rg: 2
id: kt-nielsen-maximal-rounding-gap-proof
kind: route
title: Compare the killed exact mark with its reduced free-group norm
target: kt-nielsen-models-have-maximal-exact-rounding-gap
requires:
  - kt-double-is-nielsen-semidirect-product
  - finite-dimensional-nielsen-cocycle-models-kill-mark
---

The second prerequisite applies to every exact pair `(beta_n,theta_n)` in
`(NMG2)--(NMG3)` and to the fixed `h in <<Gamma>>_G`.  It gives

```text
theta_n(b_*)=1                                            (NMP1)
```

at every stage.

Apply the strong norm condition `(SNM5)` to the two-term group-ring element
`b_*-1`.  Under `(KNS2)`, `b_*` is a nontrivial free generator of the normal
subgroup `N`, so its left regular unitary has spectrum the unit circle and

```text
||lambda_D(b_*)-1||=||lambda_N(b_*)-1||=2.                (NMP2)
```

Equations `(SNM4)--(SNM5)` therefore give

```text
||V_n(x_*)-1||->2.                                       (NMP3)
```

Combining `(NMP1)` and `(NMP3)` is exactly `(NMG4)`.  Simultaneous unitary
conjugation and finite amplification preserve this norm, so the stated
rounding obstruction follows as well.
