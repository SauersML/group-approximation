---
rg: 2
id: canonical-swap-corners-have-no-dimension-descent
kind: claim
title: Restoring a canonical swap corner's compressed actor costs the removed dimension
artifacts:
  - research/artifacts/sl3-corner-descent-dilation-budget-2026-09-05.md
distinct_from:
  canonical-arithmetic-swap-fold-gram-is-arcsine: that identifies the canonical principal-angle law; this computes the sharp dimension-versus-error cost of restoring the compressed actor to a unitary.
  unitary-corner-compressions-force-reduction: that bounds leakage when a compression is already near a unitary on its original corner; this allows an enlarged dilation space and determines the optimal padding cost.
---

Use the canonical arithmetic swap setup of
`canonical-arithmetic-swap-fold-gram-is-arcsine`. Let `P_n=(I-S_n)/2`,
`r_n=rank(P_n)`, and let `A_n=P_n H_n P_n` act on `ran(P_n)`, with its
own normalized Hilbert--Schmidt norm. Then `r_n/d_n -> 1/2`.

Let `e_n(k)` be the infimum of

```text
||A_n - P V P||_(2,r_n),
```

over unitaries `V` on a space of dimension `r_n+k`, where `P` selects
the designated original `r_n` coordinates. If `k_n/r_n -> beta in [0,1]`,
then

```text
e_n(k_n)^2 -> F(beta),
F(beta) = (2/pi) [(3/2)L - 2 sin(L) + (1/4)sin(2L)],
L = (pi/2)(1-beta).                                      (CDB1)
```

In particular, no padding gives squared limiting error
`F(0)=3/2-4/pi > 0`. If any unitary dilation has compression error `o(1)`,
then its padding obeys

```text
k_n >= (1-o(1)) r_n,
r_n+k_n >= (1-o(1)) d_n.                                 (CDB2)
```

Thus splitting the canonical model in half and then restoring the
**literal compressed denominator actor** with vanishing error does not
produce a smaller ambient model. This does not exclude an independently
constructed action on a smaller space which is not close to that compression,
and it does not construct or exclude canonical matrix models of the group.

The result is an application of the existing arcsine law and elementary
singular-value/dilation calculus, not a claim of a new general dilation
theorem or a solution of nonhyperlinearity.
