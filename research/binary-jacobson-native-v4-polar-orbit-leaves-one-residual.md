---
rg: 2
id: binary-jacobson-native-v4-polar-orbit-leaves-one-residual
kind: claim
title: The native V4 orbit fills the positive constant-head sector and leaves one explicit Jacobson residual
artifacts:
  - research/binary-jacobson-native-v4-polar-orbit-proof.md
distinct_from:
  binary-jacobson-first-alternating-polar-is-half-supported: that computes the seed polar support e z_+ Y_+; this computes its complete orbit under the two native source-row symmetries.
  binary-jacobson-constant-opposite-polar-is-finite-s3: that computes the bare opposite-root polar on the negative constant-root cut; this isolates the precise raw-range residual on which a joint use of that opposite root would still be needed.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for one full common return; this proves exactly how much of the carrier is covered by the first return and all of its immediately authenticated native conjugates.
---

**ESTABLISHED.**  Continue on the nonzero positive-tail raw range `e=F_+`
and put

```text
z=x_23(1),        Y=x_23(Q),        alpha=x_13(1),
p=e(1+z)(1+Y)/4.                                      (JV41)
```

By `binary-jacobson-first-alternating-polar-is-half-supported`, `p` is the
exact support of the first mixed polar.  Let

```text
X=x_12(Q),        b=x_12(1).                            (JV42)
```

Both words preserve `e`, commute with `alpha`, and commute with each other.
Their actions on the two support signs are

```text
X: (z,Y) |-> (-z,-Y),
b: (z,Y) |-> (alpha z,-Y).                             (JV43)
```

Hence the four conjugates of `p` by `<X,b>~=C_2 x C_2` have the following
exact supports.

On the `alpha=+1` cut they are the four mutually orthogonal joint sign
projections

```text
(z,Y)=(+,+),(-,-),(+,-),(-,+),                         (JV44)
```

and their sum is `e(1+alpha)/2`.

On the `alpha=-1` cut, the `b` and `X` actions coincide on signs.  The orbit
contains only

```text
(z,Y)=(+,+),(-,-),                                      (JV45)
```

each twice.  Consequently every direct sum or orthogonal union of the seed
polar and these three authenticated conjugates misses the explicit residual

```text
e_res=e(1-alpha)(1-zY)/4.                               (JV46)
```

Equivalently, the native orbit covers precisely `e-e_res`.

This is not merely a failure of the two chosen generators.  On `e_res` the
controlled coefficient space

```text
W=span_F2{Q,SQ,ST,S^2T}
```

has `x_13(r)=x_13(rQ)` for every `r in W`.  Therefore every source-row root
`x_12(r)`, `r in W`, preserves the product sign `zY`; none of their
conjugates of the seed can enter `(JV46)`.  Thus all source-row corrections
whose coefficients are already typed by the raw cuts are exhausted at once.

The remaining constant opposite root `x_31(1)` does not normalize the raw
range `e`: it already fails to normalize the negative cut of `x_13(Q)`, and
its conjugates of the other same-position defining roots leave the abelian
root subgroup.  Thus the internal `V_4` orbit argument above cannot simply
be enlarged by adjoining `x_31(1)`: its conjugate support is not a projection
on the same carrier without compressing back to `e`.  The constant `S_3`
polar of
`binary-jacobson-constant-opposite-polar-is-finite-s3` also does not decide
this question, because `e_res` contains the raw `SQ,S^2T` cuts absent from
that finite packet.

The only unfenced continuation along this route is therefore the genuinely
joint compression

```text
e_res x_31(1) e_res                                    (JV47)
```

(or an S/T-bearing conjugate of it), followed by an exact support and
covariance audit.  The location of the missing sector is no longer
ambiguous.

DERIVATION
binary-jacobson-native-v4-polar-orbit-proof
