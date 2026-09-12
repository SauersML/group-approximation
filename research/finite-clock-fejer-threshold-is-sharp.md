---
rg: 2
id: finite-clock-fejer-threshold-is-sharp
kind: claim
title: A bare finite clock has exactly the maximal fixed mass allowed by the Fejer threshold
distinct_from:
  unnamed-positive-density-fixed-space-is-terminal: that gives the sufficient finite-moment contradiction from excess fixed mass; this computes the exact fixed-mass ceiling for an order-M word and shows the sufficient threshold is sharp.
  embedded-group-algebra-carriers-have-no-excess-fixed-component: that treats relative commutant fixed components under arbitrary tracial embeddings; this is the elementary spectral and robust normalized-HS calculation for one finite-order clock.
---

Let `u` be an ordinary group element of exact order `M>=2`, and let

```text
e=(1/M)sum_(k=0)^(M-1)u^k.                            (FCT1)
```

In the canonical group trace, `e` is the `u=1` spectral projection and

```text
tau(e)=1/M.                                           (FCT2)
```

For every contraction `X` in a finite tracial representation exact on
`u^M=1`, if

```text
||(u-1)X||_2<=epsilon,
```

then

```text
||X||_2^2
 <=tau(e)+epsilon^2/[4 sin^2(pi/M)].                  (FCT3)
```

Consequently canonical finite-clock microstates can carry asymptotic fixed
mass at most `1/M`, and this is sharp by taking `X=e`.

The finite-order version of
`unnamed-positive-density-fixed-space-is-terminal` permits at most `N=M`,
because `u^M=1`, and requires `N alpha>1`.  The bare-clock ceiling gives

```text
N alpha<=M(1/M)=1.                                    (FCT4)
```

Thus merely replacing the infinite Britton word by a very high finite-order
clock cannot close the unnamed-carrier route.  A successful finite-clock
construction must force **excess fixed mass** strictly above the canonical
`1/M` atom by a matrix-only mechanism.  No universal group-algebra carrier
can do this: if `(u-1)p=0` for a projection `p in C[Gamma]`, faithfulness
gives `p<=e` and hence `tau(p)<=1/M`.

