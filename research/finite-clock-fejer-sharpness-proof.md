---
rg: 2
id: finite-clock-fejer-sharpness-proof
kind: route
title: Project onto the trivial clock character and use the spectral gap
target: finite-clock-fejer-threshold-is-sharp
requires: []
---

The powers `1,u,...,u^(M-1)` are distinct, so the canonical trace of their
average is `1/M`.  Standard cyclic Fourier calculus makes `e` the spectral
projection of `u` at eigenvalue one.

On `(1-e)H`, every eigenvalue of `u` is a nontrivial `M`-th root of unity.
Therefore

```text
|(u-1)| >= 2 sin(pi/M)(1-e).                          (FCT5)
```

It follows that

```text
||(1-e)X||_2
 <=epsilon/[2 sin(pi/M)].                             (FCT6)
```

The two left spectral cuts are Hilbert--Schmidt orthogonal.  Since `X` is a
contraction,

```text
||eX||_2^2=tau(X^*eX)<=tau(e).
```

Adding this to `(FCT6)` squared proves `(FCT3)`.  Equality at zero defect is
attained by `X=e`.  The comparison with the largest admissible Fejer order
is then exactly `(FCT4)`.

