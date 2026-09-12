---
rg: 2
id: contraction-coarea-clipping-proof
kind: route
title: Use Hilbert--Schmidt divided differences instead of unitary conjugation
target: low-gap-cut-and-spike-dichotomy-holds-for-contractions
requires: []
---

The spectral coarea identity used in the bounded theorem is stated for
every matrix `A`:

```text
integral ||[1_[t,infinity)(x),A]||_2^2 dt
 <=||[x,A]||_2 ||A||_2.
```

For a contraction, `||A||_2<=1`, so the original summation and
Cauchy--Schwarz proof gives exactly the same common-cut estimate.  The trace
balance argument involves only the distribution of `x` and is unchanged.

For clipping, diagonalize `x`.  For every scalar 1-Lipschitz function `f`
and arbitrary matrix `A`,

```text
[A,f(x)]_(ij)=(f(lambda_j)-f(lambda_i))A_(ij),
[A,x]_(ij)=(lambda_j-lambda_i)A_(ij).
```

Termwise comparison and summation give

```text
||[A,f(x)]||_2<=||[A,x]||_2.
```

The remainder of the clipping proof is scalar truncation, normalization,
and the contraction-level bounded theorem just proved.  Hence all constants
are unchanged.
