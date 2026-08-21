---
rg: 2
id: iwahori-square-root-presentation-is-bs14-plus-one-involution
kind: claim
title: The corrected Iwahori square-root presentation is BS(1,4) plus one involution and two cubic constraints
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-question-as-square-root-of-parabolic: that gives the two modular charts and the exact root--involution equations; this eliminates the second-chart involution without losing a relation and exposes the complete BS(1,4) skeleton.
  parabolic-spectrum-is-doubling-invariant: that extracts one conjugation relation from the arithmetic matrices; this proves that the relation is part of an equivalent five-relator presentation of the full group.
---

Put `T=xy` in the corrected square-root presentation `(SR2)` from
`iwahori-question-as-square-root-of-parabolic`:

```text
x^2=1,  y^3=1,  s^2=T,  e^2=1,
(es)^3=1,  xy^2xyx=s^2 e s e.                         (B1)
```

Define `r=xe`.  Then `(B1)` is equivalent to

```text
SL_2(Z[1/2])/{+-I}
 = <x,r,s | x^2=1, (xr)^2=1, (x s^2)^3=1,
             r s r^(-1)=s^4, (x r s)^3=1>.            (B2)
```

Thus `<r,s>` is the canonical `BS(1,4)` skeleton, and the entire
non-amenable coupling consists of one involution `x`, its inversion relation
`xrx=r^(-1)`, and the two order-three constraints `(x s^2)^3=1` and
`(xrs)^3=1`.

## Proof

Using `T=xy` and hence `y=xT`, one has

```text
xy^2xyx = T x T^2 x.                                  (B3)
```

The last equation of `(B1)`, together with `s^2=T`, therefore cancels the
leftmost `T` and gives

```text
e s e = x T^2 x.                                      (B4)
```

Since `r=xe` and `r^(-1)=ex`, equation `(B4)` gives

```text
r s r^(-1)=x(e s e)x=T^2=s^4.                         (B5)
```

Moreover `e=xr`, so `e^2=1` is exactly `(xr)^2=1`; `y=xs^2`, so `y^3=1`
is exactly `(xs^2)^3=1`; and `(es)^3=1` is exactly `(xrs)^3=1`.  This proves
that `(B1)` implies `(B2)`.

Conversely, from `(B2)` set `e=xr`, `T=s^2`, and `y=xT`.  The first four
relations in `(B1)` and `(es)^3=1` are immediate.  From
`rsr^(-1)=s^4=T^2` and `(xr)^2=1` (so
`e=xr=e^(-1)=r^(-1)x`) one obtains

```text
e s e=x r s r^(-1)x=xT^2x.
```

Multiplying by `T` and applying `(B3)` recovers
`xy^2xyx=s^2ese`.  Hence the presentations are equivalent.

In the standard arithmetic matrices, `s` is the half-parabolic
`[[1,1/2],[0,1]]` and `r` is the diagonal element
`diag(2,1/2)` up to the central sign, so `(B5)` is literally the
times-four action on the dyadic parabolic.

## Consequence for the open stability problem

The metabelian core `<r,s>=BS(1,4)` is HS-stable through the one-solenoid
dense-periodic-measures theorem recorded in
`far-sector-is-solenoid-measure-rigidity`.  Therefore the abelian spectrum
and the times-four implementer can be repaired together.  What remains is a
relative extension theorem: after repairing `(r,s)`, repair one involution
`x` while preserving both cubic constraints.  Any far-sector argument that
still treats the dyadic parabolic alone as the obstruction is attacking a
settled subproblem; the load-bearing datum is the simultaneous pair of
triangle constraints in `(B2)`.
