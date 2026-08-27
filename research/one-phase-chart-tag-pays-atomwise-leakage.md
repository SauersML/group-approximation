---
rg: 2
id: one-phase-chart-tag-pays-atomwise-leakage
kind: claim
title: One injective phase tag pays the complete atomwise section leakage
distinct_from:
  phase-covariance-words-exactly-measure-type-transport-leakage: that gives the general two-sided phase-code identity for complete PVMs; this incorporates partial carrier projections, separates the existing conductor first exit, and targets the exact EDA11 sum.
  equal-rank-denominator-edges-authenticate-decoded-atoms: that turns an already bounded EDA11 sum into cross-chart saturation; this supplies a single mixed chart observable whose covariance bounds that sum.
  independent-chart-refinement-forces-eda-leakage: that proves marginal carrier/root ledgers cannot imply EDA11; this identifies the minimal non-marginal phase covariance which detects its tensor counterpacket.
---

Let `(E_i)_(i=0)^(q-1)` and `(F_i)_(i=0)^(q-1)` be partial PVMs in a
finite tracial von Neumann algebra, with

```text
sum_i E_i=R,              sum_i F_i=S.                 (OPT1)
```

Let `T` be unitary, let `zeta=exp(2 pi i/q)`, and form the partial phase tags

```text
A=sum_i zeta^i E_i,       B=sum_i zeta^i F_i.          (OPT2)
```

After absorbing any prescribed label bijection into the indexing of the
`F_i`, put

```text
L=||(1-S)TR||_2^2,
K=||BTR-TA||_2^2,
Xi=sum_i||(1-F_i)TE_i||_2^2.                           (OPT3)
```

Then the exact block identities are

```text
K=L+sum_(i,j)|zeta^j-zeta^i|^2||F_jTE_i||_2^2,
Xi=L+sum_(i!=j)||F_jTE_i||_2^2.                        (OPT4)
```

Consequently, with `gamma_q=4 sin^2(pi/q)`,

```text
Xi<=L+(K-L)/gamma_q<=L+K/gamma_q.                      (OPT5)
```

For the native shell `q=42`, this is a fixed dimension-free constant

```text
gamma_42^(-1)=1/(4 sin^2(pi/42)).                      (OPT6)
```

Thus one section-covariant injective phase tag per chart is sufficient to
derive the full atomwise leakage hypothesis needed by `(EDA13)`. The
independent-coordinate counterpacket pays `K` at the same fixed scale, so
it no longer escapes.

This does not by itself construct or wordize `A,B`. If the chart atoms come
from an exact commuting one-hot/Fourier packet, `(OPT2)` is a fixed linear
combination of its Fourier atoms and the estimate is available. The precise
remaining arithmetic question is whether the actual mixed-root packet
controls `||BTR-TA||_2`; separate conductor bands, raw incidence, and chart
marginals do not, by
`independent-chart-refinement-forces-eda-leakage`.
