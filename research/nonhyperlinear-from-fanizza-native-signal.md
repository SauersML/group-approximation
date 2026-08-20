---
rg: 2
id: nonhyperlinear-from-fanizza-native-signal
kind: route
title: Apply the reverse Kleene diagonal to the groupified native Fanizza signal
target: non-hyperlinear-group
requires:
  - kleene-halting-mark-collapse-diagonal
  - fanizza-signal-involution-is-native-mark
  - fanizza-native-signal-groupification
  - fanizza-et-al-computable-bcs-signal-family
artifacts:
  - research/artifacts/fanizza-native-signal-diagonal-2026-08-20.md
---

Use `w_m=d_m=x_(D,m)`.  If machine `m` halts, clause 1 of the weakened
groupifier supplies one exact representation with `w_m!=I`, hence
`w_m!=1` algebraically in `Gamma_m`.  No trace on this representation is
used.

If `m` does not halt, combine `(NSG1)--(NSG2)` with `(NSM2)`:

```text
||U(w_m)-I||_2
 <= B_m eta+||X_(D,m)-I||_2
 <= (B_m+2sqrt(C_m A_m)) eta
 =K_m eta.                                                       (NFD1)
```

All constants in `K_m` are computable from `m`.  Set

```text
alpha_m=1,                 delta_m=1/(1+K_m).
```

Then `eta<delta_m` implies `||U(w_m)-I||_2<1<sqrt(2)`.  The compiler therefore
satisfies `(KHC1)--(KHC3)`, and
`kleene-halting-mark-collapse-diagonal` effectively produces a finitely
presented nonhyperlinear group.
