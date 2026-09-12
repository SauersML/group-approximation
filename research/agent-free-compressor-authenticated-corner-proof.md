---
rg: 2
id: agent-free-compressor-authenticated-corner-proof
kind: route
title: Telescope the finite Reynolds averages across the approximate stable-letter intertwiner
target: agent-free-compressor-authenticated-corner-pays-hs
requires: []
---

Let

```text
R_B=|B_f|^(-1) sum_(g in B_f) B_g,
R_A=|A_f|^(-1) sum_(a in A_f) A_a.                    (ACQ1)
```

These are the exact Reynolds projections on `eH`.  The fixed generator and
word lists make `(ACP2)--(ACP4)` telescope to

```text
||(T R_B T^(-1)-R_A)e||_2<=C_1(delta+epsilon).         (ACQ2)
```

Commuting `e` past `T` costs another fixed multiple of the reduction error.
Since normalized trace is invariant under unitary conjugacy,

```text
|tr(e R_B)-tr(e R_A)|<=C_2(delta+epsilon).             (ACQ3)
```

One may obtain `(ACQ3)` directly from Cauchy--Schwarz,
`|tr(X)|<=||X||_2`, after extending both corner projections by zero on
`(1-e)H`.  Combining `(ACQ3)` with the fixed packet inequality `(ACP1)` gives
`(ACP5)`.  Every word length and averaging denominator is fixed, so no
constant depends on matrix dimension.
