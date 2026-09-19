---
rg: 2
id: shared-endpoint-r2-r3-anchor-has-linear-seam-bound
kind: claim
title: A genuinely shared R2 endpoint or R3 complement gives a linear pointwise seam bound
distinct_from:
  bare-r5-a6-collision-does-not-synchronize-shared-labels: that shows the nonshared R5 collision is blind to a permutation of the two common labels; this identifies the exact extra endpoint datum which is sufficient to remove that gauge.
  common-pivot-r2-r3-data-preserve-a6-label-swap: that countermodel shares only the permutation-invariant pivot and keeps all label arms contextual; this requires the transported output, or the split parent and complementary child, to be literally common to both occurrences.
  pointwise-a5-overlap-globalizes-carmichael-family: that globalizes an already-proved adjacent-chart comparison; this is the dimension-free two-occurrence estimate which can supply that comparison.
---

Let all displayed matrices be unitaries and use normalized Hilbert--Schmidt
norm.  Either of the following two pieces of genuinely shared endpoint data
synchronizes contextual occurrences `X,X'` with no dimension loss.

For an R2-shaped transport anchor, if

```text
||P^* X P-Q||_2 <= eta,        ||P^* X' P-Q||_2 <= eta,          (SEA1)
```

then

```text
||X-X'||_2 <= 2 eta.                                            (SEA2)
```

For an R3-shaped split anchor, if

```text
||C-XD||_2 <= eta,             ||C-X'D||_2 <= eta,               (SEA3)
```

then the same estimate `(SEA2)` holds.  Here `C` is the shared coarse
parent and `D` is the shared complementary child; no commutativity or order
assumption is needed for the estimate.

Consequently, suppose two contextual Carmichael cycles use the same pivot
arm `R` and obey

```text
||Y-XR||_2 <= zeta,             ||Y'-X'R||_2 <= zeta.             (SEA4)
```

If their label arms satisfy either `(SEA1)` or `(SEA3)`, then

```text
||Y-Y'||_2 <= 2 eta+2 zeta.                                    (SEA5)
```

Thus one *paired* R2 transport or R3 split comparison really does kill the
five-dimensional label-swap gauge and gives the exact kind of
dimension-free local inequality needed at an adjacent A5 seam.  The word
geometric problem is not this analytic estimate: it is to expose the same
endpoint matrices on both contextual occurrences using boundedly many
conjugates of the fixed Bleak--Quick relations.

