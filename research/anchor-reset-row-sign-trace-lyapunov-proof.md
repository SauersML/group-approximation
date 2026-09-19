---
rg: 2
id: anchor-reset-row-sign-trace-lyapunov-proof
kind: route
title: Resolve the reset into three sign blocks and telescope the exact flow
target: anchor-reset-row-sign-trace-is-sharp-lyapunov
requires:
  - spectral-cut-anchor-reset-pays-boundary-in-one-row
  - odd-spectral-anchor-resets-have-monotone-sign-budget
---

Since `p` commutes with `A`, the projections `s=pe`, `r=(1-p)e`, and
`t=1-e` are mutually orthogonal and sum to one.  Also

```text
 A=1-2(s+r),       A'=1-2r.                             (ARP1)
```

For any projection `f` and reflection `B`, block decomposition across
`f+(1-f)` gives

```text
 ||[1-2f,B]||_2^2=8||(1-f)Bf||_2^2.                   (ARP2)
```

Use `(ARP2)` first with `f=s+r` and then with `f=r`.  Orthogonality and
traciality eliminate the cross terms, giving

```text
 ||[A,B]||_2^2 =8(||tBs||_2^2+||tBr||_2^2),
 ||[A',B]||_2^2=8(||sBr||_2^2+||tBr||_2^2).            (ARP3)
```

Because `B=B*`, `||sBr||_2=||rBs||_2`.  Since `B` is unitary,

```text
 tau(s)=||Bs||_2^2
       =||sBs||_2^2+||rBs||_2^2+||tBs||_2^2.           (ARP4)
```

Subtract `(ARP3)`, average over `B_k`, and subtract the lost trace
`tau(s)=tau(e)-tau(r)`.  Equations `(ARL2)--(ARL3)` follow exactly.

For sharpness, `(ARL4)` has `s=p`, `r=1-p`, `t=0`, and `B` interchanges
`s` and `r`.  Directly `(ARP3)` gives energy increase
`8tau(s)=4`, proving that no smaller universal coefficient works.
