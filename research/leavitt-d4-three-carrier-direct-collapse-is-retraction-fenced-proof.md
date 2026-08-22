---
rg: 2
id: leavitt-d4-three-carrier-direct-collapse-is-retraction-fenced-proof
kind: route
title: Identify the target projections with cyclic shifts of the two source projections
target: leavitt-d4-three-carrier-direct-collapse-is-retraction-fenced
requires:
  - leavitt-d3-length15-retraction-fence
---

Use the representative sign path

```text
(-,-,-,+,+,+,+,+,+,+).
```

Its orbit valences are `(3,3,3,1)`.  Write the ten coefficient slots as
`g0,...,g9`, solve the unary orbit as `z=H^-1`, and denote the projections of
its coefficient corner onto the four free coefficient copies by

```text
U=H0=g7 g3,       V=H1=g8 g2 g4,
W=H2=g9 g1 g5,    X=H3=g0 g6.                          (1)
```

The three residual sign words are all `(-,+,+)`.  Suppose, after a cyclic
choice of labels, that `R0=R2=1`.  Project `R2` onto copy 0.  Its equation is

```text
g4 U^-1 g8 g2=1,
```

and therefore `V=g8 g2 g4=U`.  Projection of `R2` onto copy 1 similarly
gives `W=V`.  Projection of `R0` onto copy 0 gives

```text
g6 U^-1 g0=1,
```

and hence `X=g0g6=U`.  Thus

```text
U=V=W=X.                                                    (2)
```

Now project the remaining residual `R1` onto each copy.  After `(2)`, its
four projected words are not new: they are exactly cyclic shifts of source
projections,

```text
(R1)_0=(R2)_1,   (R1)_1=(R0)_0,
(R1)_2=(R0)_1,   (R1)_3=(R0)_2.                            (3)
```

Every word on the right of `(3)` is the identity.  Hence all four free-copy
retractions of `R1` are trivial.  In particular `R1` cannot be the reduced
one-copy word `h_j` for any `j` when `h != 1`.

For completeness, take the adjacent sources `R0=R1=1`.  Their projections
first give `U=V=W=X`.  The only apparently order-sensitive target projection
is

```text
(R2)_0=g4 U^-1 g8 g2.
```

But the source equation `(R0)_2=1` is

```text
U(g2 g4)U^-1g8U^-1=1,
```

so `g4U^-1g8=g2^-1` and `(R2)_0=1`.  The other three target projections are
immediate copies of source equations.  For the remaining adjacent pair
`R1=R2=1`, the same projections give `U=V=W=X`; then `(R0)_0,(R0)_1` are
literal source projections, while

```text
(R2)_0=1  implies (R0)_2=1,
(R2)_1=1  implies (R0)_3=1
```

by the same one-line cyclic cancellation.  Hence all three choices of two
source residuals are fenced.  No restriction on the coefficient units was
used.
