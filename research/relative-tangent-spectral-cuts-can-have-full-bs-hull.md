---
rg: 2
id: relative-tangent-spectral-cuts-can-have-full-bs-hull
kind: claim
title: A rank-two spectral cut of a relative reflection tangent can generate the whole BS packet
distinct_from:
  bs14-residual-invariant-hull-has-unbounded-packet-loss: that starts from a raw residual carrier; this realizes the same explosion for the high singular carrier of a legitimate tangent to the fixed-R inversion manifold.
  long-bs14-packets-defeat-invariant-op-thresholding: that compares exact BS cores which are HS-close and operator-far; this keeps one exact core fixed and refutes spectral truncation of its linear correction.
  low-rank-reflection-surgery-preserves-the-exact-bs-core: that permits a non-invariant low-rank reflection change while accepting small word defects; this proves such a cut cannot be made into an exact reducing active block by taking its BS hull cheaply.
---

**ESTABLISHED.**  On arbitrarily long simple fourth-power packets there is
a legitimate anti-Hermitian tangent `h` to the fixed-`R` inversion manifold
such that

```text
[h,R]=0,                 XhX=-h,                       (RTF1)
rank 1_(0,infinity)(|h|)=2,                            (RTF2)
```

but the invariant hull of that spectral projection under the exact
`BS(1,4)` core `(R,S)` is the entire packet.  Consequently an off-zero
normalized-HS normal splitting cannot be upgraded to the passive Newton
step merely by spectrally truncating its correction and moving the high
support into the active ledger.

The point is that the exact relative constraints on the reflection are

```text
X^2=1,                    XRX=R^(-1).                  (RTF3)
```

For a chart `X exp(h)`, their tangent equations are precisely the two
relations in `(RTF1)`.  They do **not** imply `[h,S]=0`; the two cubic rows
are what constrain the interaction with `S`.

The route `fourier-relative-tangent-has-full-bs-hull` gives the explicit
packet calculation.  It also shows why gauge optimization does not remove
the example: `h` changes the reflection over the fixed core and is not a
common-conjugation motion of the core.

Thus the mixed-norm requirement in
`passive-iwahori-off-zero-cb-normal-splitting` cannot be replaced by a
generic Chebyshev cut of an L2 correction.  A weaker surviving theorem would
have to use additional arithmetic information from the cubic rows to select
a correction whose high spectral carrier has a sublinear **full BS hull**;
plain tangent equivariance supplies only `R`-invariance.

