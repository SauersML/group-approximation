---
rg: 2
id: compressed-reflection-even-cesaro-proof
kind: route
title: Control leakage from the compression and telescope powers to the two-cycle
target: compressed-reflection-kills-even-cesaro-mark
requires: []
---

Write `A=QWQ`.  The two off-diagonal blocks of a unitary have the same
normalized Hilbert--Schmidt norm, and hence

```text
||QW(1-Q)||_2^2
 = tau_d(Q)-||A||_2^2
 = ||(1-Q)WQ||_2^2.                                  (CRC1)
```

Since `||V||_2=sqrt(tau_d(Q))` and `||A||_2<=sqrt(tau_d(Q))`, the difference
of squares and Cauchy--Schwarz give

```text
tau_d(Q)-||A||_2^2
 <= ||V-A||_2 (||V||_2+||A||_2)
 <= 2epsilon.                                         (CRC2)
```

The orthogonal block decomposition of `QW-VQ` now yields

```text
delta^2:=||QW-VQ||_2^2 <= epsilon^2+2epsilon.          (CRC3)
```

Telescoping one power at a time gives, for `k>=0`,

```text
||QW^k-V^kQ||_2 <= k delta.                            (CRC4)
```

Indeed the difference at level `k` is

```text
(QW-VQ)W^(k-1)+V(QW^(k-1)-V^(k-1)Q),
```

and left multiplication by the partial unitary `V` is contractive in
Hilbert--Schmidt norm.

If `t` is even, `V^2=Q` gives

```text
sum_(k=0)^(t-1) V^k Q = (t/2)(Q+V).                   (CRC5)
```

Moreover `(Q-V)(Q+V)=0`.  Sandwiching `(CRK1)` by `Q+V` shows
`D^(1/2)(Q+V)=0`.  Since `D=QDQ` and `||D^(1/2)||<=1`, equations
`(CRC4)--(CRC5)` imply

```text
||D^(1/2) Sigma_t(W)||_2
 <= sum_(k=0)^(t-1) ||QW^k-V^kQ||_2
 <= (t(t-1)/2) delta.
```

Squaring and applying `(CRC3)` proves `(CRK2)`.
