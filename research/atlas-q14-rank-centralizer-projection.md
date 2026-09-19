---
rg: 2
id: atlas-q14-rank-centralizer-projection
kind: claim
title: The q14 rank defect linearly projects the second transvection into the first centralizer
distinct_from:
  atlas-q14-forces-t30-covariance-floor: that is a normalized-Hilbert--Schmidt energy wall in regular complex representations; this is an exact characteristic-two rank-metric block calculation on repeated natural modules.
  atlas-literal-augmented-residual-count-is-fourteen: that counts q14 as one literal residual; this analyzes that residual but does not handle the other thirteen.
  atlas-left-ideal-rank-nonwandering: that asks for a common invariant quotient for the full augmented packet; this only gives a linear centralizer correction for q14 and deliberately does not preserve the second full chart representation.
---

ESTABLISHED.  Let `E=F2^(4m)` and let

```text
x=1+N,       y=1+M,
N^2=M^2=0,   rank N=rank M=m.                       (QRP1)
```

These are the two repeated-natural transvections occurring in q14.  Put

```text
q=(xy)^2,       d=rank(q-1).                          (QRP2)
```

Then

```text
d=rank(NM-MN).                                        (QRP3)
```

There is an endomorphism `M_0` such that

```text
[N,M_0]=0,
rank(M-M_0)<=4d,
rank(M_0^2)<=8d.                                      (QRP4)
```

Equivalently, `y_0=1+M_0` commutes exactly with `x`, lies at rank distance
at most `4d` from `y`, and has involution defect of rank at most `8d`.

This is the strongest correction supplied by q14 through linear block
algebra alone.  It does **not** assert that `M_0^2=0`, that `rank M_0=m`, or
that `1+M_0` extends to a conjugate copy of the whole second `A8` chart.
Those are nonlinear relative-module requirements.  Thus q14 can be absorbed
at constant rank cost into the linear centralizer, but using the
thirteen post-q14 filling residuals still requires a relative `V4` rank
correction preserving the marked chart type.

### Proof

Since `x` and `y` are involutions, right multiplication by `yx` gives

```text
(q-1)yx=xy-yx=NM-MN,
```

which proves `(QRP3)`.

Choose

```text
E=P direct_sum Q direct_sum R,
P=im N,
N:Q -> P an isomorphism,
dim P=dim Q=m,  dim R=2m.                             (QRP5)
```

In these coordinates `N_(P,Q)=1` is its only nonzero block.  If
`Z=(Z_ij)`, the equation `[N,Z]=0` is exactly

```text
Z_QP=0,   Z_QR=0,   Z_RP=0,   Z_QQ=Z_PP.             (QRP6)
```

Each of the four discrepancies in `(QRP6)` occurs as a rectangular
compression of `[N,Z]`.  Set those three off-diagonal blocks to zero and
replace `Z_QQ` by `Z_PP`, leaving every other block unchanged.  The result
`Pi_N(Z)` commutes with `N`, and rank subadditivity gives

```text
rank(Z-Pi_N(Z))<=4 rank([N,Z]).                       (QRP7)
```

Apply this to `Z=M` and call the result `M_0`.  If
`Delta=M_0-M`, then

```text
M_0^2-M^2=M_0 Delta+Delta M,
```

so `rank(M_0^2)<=2 rank Delta<=8d`, proving `(QRP4)`.
