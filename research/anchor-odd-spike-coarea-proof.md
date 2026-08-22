---
rg: 2
id: anchor-odd-spike-coarea-proof
kind: route
title: Bound odd-square covariance and apply spectral coarea
target: one-anchor-odd-spike-has-a-cheap-reducing-cut
requires:
  - covariant-square-function-has-common-reducing-threshold
  - block-adaptive-sparse-reset-is-cheap
---

Expand the commutator of `Y_(a,i)` with `Q_l`, then the commutator of its
square, to obtain `(OSC6)`.  Average over `l` by Cauchy--Schwarz.  Apply the
spectral coarea identity on the interval `[t,2t]`; its length is `t`, giving
`(OSC3)`.  Markov and the identity
`tau(R_(a,i))=||[Q_a,Q_i]||_2^2/4` give `(OSC2)`.  The ordinary
cosine--sine correction makes the cut reducing, and block-adaptive reset on
that cut supplies the final repair estimate.  The Laurent formula
`4R=2-(Q_aQ_i)^2-(Q_aQ_i)^(-2)` shows that the cut already commutes with
the anchor and reset site; leave those two generators fixed so the
complementary operator bound persists.
