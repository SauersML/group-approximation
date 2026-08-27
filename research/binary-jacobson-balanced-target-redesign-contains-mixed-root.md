---
rg: 2
id: binary-jacobson-balanced-target-redesign-contains-mixed-root
kind: claim
title: A balanced Jacobson target redesign contains the mixed T-root but moves the center beyond the raw cut algebra
artifacts:
  - research/binary-jacobson-balanced-target-redesign-proof.md
distinct_from:
  binary-jacobson-constant-weyl-target-redesign-moves-off-residual: that proves constant Weyl conjugation cannot produce a T coefficient; this uses a literal balanced S/T involution and does produce the mixed root.
  binary-jacobson-first-alternating-polar-is-half-supported: that computes the support of the compression of x_21(T); this embeds that same occurrence as a named generator of a conjugate M4 target packet.
  binary-jacobson-positive-tail-fold-is-a-literal-degree-two-tuple: that supplies the literal degree-two source on the raw range; this gives a new literal degree-four target candidate but isolates its still unauthenticated moved-center carrier.
---

**ESTABLISHED.**  Let

```text
D=(x_12(Q),x_23(1),x_14(Q),x_43(1)),
w=x_13(Q),
```

and let `g` be the balanced involution acting on coordinates `(1,3)` by

```text
[[Q,S],[T,0]]
```

and fixing coordinates `2,4`.  Then

```text
gDg=(x_12(Q),x_21(T),x_14(Q),x_41(T)).                  (JBT1)
```

In particular the mixed occurrence `u=x_21(T)` from the first alternating
closure relation is a literal Pauli generator of this redesigned packet.
The tuple still generates `M_4 tensor I` on the negative cut of its common
center because it is an exact conjugate of the native packet.

The moved marked center is explicit:

```text
c_T=gwg=I+QT E_11.                                      (JBT2)
```

It is an involution conjugate to the original marked root.  It commutes with
`w`, but it does not belong to the abelian root algebra defining the raw
range and it fails to commute with the `x_13(SQ)` cut:

```text
c_T x_13(SQ)c_T=x_13(Q)x_13(SQ).                        (JBT3)
```

In fact this gives the exact carrier relation

```text
F_+ c_T F_+=0.                                          (JBT4)
```

Indeed both `x_13(Q)` and `x_13(SQ)` act as `-1` on `F_+`, whereas `(JBT3)`
turns the second required negative sign into their product, which acts as
`+1`.  Thus `c_T` carries the raw range into an orthogonal sign sector.

Therefore `(JBT1)` solves the **literal-occurrence** part of the mixed-root
target redesign, but not the carrier part.  The established support of
`F_+x_21(T)F_+` lies inside `F_+`, while the redesigned center moves that
whole carrier off itself.  A closing argument must therefore become a
rectangular two-carrier construction and show that the polar transports a
nonzero raw subcut onto the appropriate moved negative-center carrier (then
audit the other three rows); merely replacing `D` by `gDg` is insufficient.

This is strictly closer than a constant-Weyl redesign: the desired mixed
word is now one of the four target generators, and the remaining typing
problem is the explicit orthogonal carrier move and its covariance on the
selected polar support.

DERIVATION
binary-jacobson-balanced-target-redesign-proof
