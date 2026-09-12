---
rg: 2
id: raw-simple-weyl-rectangle-calculation-proof
kind: route
title: Compare the two simple-Weyl section paths before decoding
target: sl3-raw-weyl-rectangle-pins-only-equal-rank-corners
requires:
  - raw-denominator-incidence-kills-off-diagonal-shell-orbit
  - balanced-raw-lamp-orbit-cannot-approximate-shell-pvm
---

# Compare the two simple-Weyl section paths before decoding

Using `(RWR1)` and `[P,rho(w)]=0`,

```text
rho(w)rho(h)P rho(w)^*
 =rho(w)rho(h)rho(w)^*P
 =rho(h_w)P.
```

This proves `(RWR4)`, after which `(RWR5)--(RWR6)` are immediate.  For an
approximate assignment, the same calculation has only the two errors in
`(RWR7)`.  Bi-invariance of normalized Hilbert--Schmidt norm gives the first
bound in `(RWR8)`, and a two-factor telescoping gives the second.

For `(RWR9)`, use `X_wX_w^*=A_w`:

```text
||E_wX_w||_2^2=tau(E_wA_w).
```

Since `E_w,A_w` are projections of the same trace,

```text
||E_w-A_w||_2^2
 =tau(E_w)+tau(A_w)-2tau(E_wA_w)
 =2(tau(P)-||E_wX_w||_2^2).
```

Without equal rank, `tau(E_wA_w)<=tau(E_w)` gives `(RWR10)`.  The stated
shell and raw-atom traces are the established rank calculation in
`balanced-raw-lamp-orbit-cannot-approximate-shell-pvm`.
