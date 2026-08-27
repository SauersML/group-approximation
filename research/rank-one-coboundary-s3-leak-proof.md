---
rg: 2
id: rank-one-coboundary-s3-leak-proof
kind: route
title: Realize all raw denominator and coboundary identities with two transpositions
target: rank-one-self-commutator-coboundary-packet-has-s3-leak
requires: []
---

In `S_3`, set

```text
u=x=y=(12),          h=(23),          c=1.              (RCP1)
```

Then `u` commutes with `x`, `y`, and `c`. Moreover

```text
z=h y h^(-1)=(13),
x z x c=(12)(13)(12)=(23)=h.                            (RCP2)
```

Thus all identities in `(RCB1)--(RCB2)`, including the original
denominator decomposition rather than merely its derived self-commutator,
hold exactly. On the other hand

```text
w=[u,h]=u h u^(-1) h^(-1)
```

is a nonidentity three-cycle. Apply the left regular representation of
`S_3`. Every displayed group identity becomes an exact unitary identity,
and the normalized trace of the regular matrix of a nonidentity element is
zero. Hence `|tr(W)|=0`, proving the claim.

For completeness, the derived packet is also automatically present.
Conjugation by `z=(13)` inverts the three-cycle `w`, and `x` conjugates it
back, so `w=x[w,z]x^(-1)`; also `z^4=x^2=1`. This recovers the earlier
`S_3` calibration while showing that none of the discarded variables was
responsible for its escape.

