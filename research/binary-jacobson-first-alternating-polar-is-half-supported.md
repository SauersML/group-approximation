---
rg: 2
id: binary-jacobson-first-alternating-polar-is-half-supported
kind: claim
title: The first full-cycle Jacobson polar is supported on only one native Pauli sign
artifacts:
  - research/binary-jacobson-first-alternating-polar-support-proof.md
distinct_from:
  binary-jacobson-first-alternating-ts-closure-relation: that identifies the first explicit full-cycle relation and proposes its T-root compression; this computes that compression's exact support on the positive-tail raw range.
  binary-jacobson-constant-opposite-polar-is-finite-s3: that fences the bare constant opposite-root polar inside a finite packet; this uses the genuinely mixed root x_21(T), but shows its first raw-range polar is rank deficient.
  binary-jacobson-positive-tail-fold-is-a-literal-degree-two-tuple: that puts the degree-two and degree-four tuples on the same carrier; this proves the most direct common-return candidate cannot be a coisometry on that carrier.
---

**ESTABLISHED.**  Let `e=F_+` be any nonzero positive-tail raw range from
`binary-jacobson-positive-tail-fold-is-a-literal-degree-two-tuple`, and put

```text
s=rho(x_13(S)),          z=rho(x_23(1)),
u=rho(x_21(T)),          A=e u e.                       (JAP1)
```

Then

```text
s e=-e,                  [u,s]=z,            [u,z]=1.   (JAP2)
```

Consequently

```text
zA=A=Az.                                                   (JAP3)
```

Thus both support projections of `A`, and hence the polar of `A`, lie in the
positive `z` cut

```text
e_+=e(1+z)/2.                                             (JAP4)
```

The two `z` signs inside `e` have equal nonzero rank.  Indeed the literal
native word `x_12(Q)` preserves `e` and conjugates `z` to `x_13(Q)z=-z` on
the negative head cut.  Therefore

```text
rank(e_+)=rank(e)/2,
rank(supp(A))<=rank(e)/2.                                 (JAP5)
```

There is no hidden small-singular-value issue.  The projections `e` and
`u e u` commute, so

```text
A^2=e(u e u)=e meet (u e u)
   =e (1+z)/2 (1+Y)/2,        Y=rho(x_23(Q)).             (JAP6)
```

is a projection.  Hence `A` is already a self-adjoint partial isometry and
its polar support is exactly the intersection in `(JAP6)`.

In particular the polar of the compression suggested by the first
alternating `TS` relation can never satisfy

```text
polar(A) polar(A)^*=e.
```

It cannot be the common coisometric PI return.  The exact support formula
also identifies the complementary occurrence problem: one must cover the
other three joint `(z,Y)` signs, not merely insert an arbitrary phase.  The relation is genuinely
mixed and load-bearing at the coefficient level, but one must pair its
`z=+1` support with an authenticated complementary occurrence on the
`z=-1` half (or select a different square return).  A single full-cycle
polar is now ruled out exactly.

DERIVATION
binary-jacobson-first-alternating-polar-support-proof
