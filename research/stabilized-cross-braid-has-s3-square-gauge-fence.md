---
rg: 2
id: stabilized-cross-braid-has-s3-square-gauge-fence
kind: claim
title: The complementary stabilized cross braid has an S3-square gauge fence
artifacts:
  - research/stabilized-cross-braid-coefficient-proof.md
distinct_from:
  complementary-private-weyl-loops-have-s3-square-gauge-model: that uses diagonal branch Whiteheads on one coordinate pair; this stabilizes each cross-branch Whitehead through a private third coordinate and computes all three complementary fusion rows.
  cross-branch-partial-whiteheads-have-finite-wreath-gauge-model: that computes the coarse cross words directly on `(7,8)`; this tests their proposed three-channel braid factorization and corrects the two nonconstant fusion coefficients.
  two-distinct-rank-two-channels-cannot-factor-cross-return: that rules out a product of two distinct rank-two channels; this is the first live three-occurrence factorization through a stable third coordinate.
---

**ESTABLISHED STABILIZED-BRAID FENCE.**  Put

```text
p=s_0t_1,       r=s_1t_0,       q_i=s_it_i,
u=p+r,          u^2=1.                                      (SCB1)
```

On stable coordinates `(7,8,9)`, define

```text
P_0=W_79(q_0,q_0),       Q_0=W_89(r,p),
P_1=W_79(q_1,q_1),       Q_1=W_89(p,r).                (SCB2)
```

Direct three-by-three multiplication verifies the positive part of the
proposed factorization:

```text
K_0=W_78(p,r)=P_0Q_0P_0=Q_0P_0Q_0,
K_1=W_78(r,p)=P_1Q_1P_1=Q_1P_1Q_1.                    (SCB3)
```

The complementary packets also cross-commute:

```text
[P_0,P_1]=[Q_0,Q_1]=[P_0,Q_1]=[P_1,Q_0]=1.            (SCB4)
```

However, two of the three advertised constant fusion rows are false.  The
exact coefficients are

```text
P_0P_1=w_79(1),
Q_0Q_1=w_89(u),
K_0K_1=w_78(u),                                       (SCB5)
```

not `w_89(1)` and `w_78(1)`.  Indeed `p+r=u` is the nonconstant binary
branch-flip unit; it is an involution but is not one.  The aggregate rows
still form the expected stabilized braid:

```text
w_79(1)w_89(u)w_79(1)=w_78(u).                        (SCB6)
```

Thus `(SCB3)` is a genuine literal three-channel occurrence table, but it
does not erase the two nonconstant objects.  Only the `P` fusion is a
constant native Weyl; the `Q` and `K` fusions retain the same branch-flip
coefficient.

The complete table has an exact finite reservoir model.  In
`S_3 times S_3`, choose reflections

```text
a=(1 2),        b=(2 3),        c=aba=(1 3),

P_0=(a,1),      Q_0=(b,1),      K_0=(c,1),
P_1=(1,a),      Q_1=(1,b),      K_1=(1,c).             (SCB7)
```

All braid and cross-commutation rows `(SCB3)--(SCB4)` hold exactly.  The
three fused gauges are the diagonal reflections

```text
A=(a,a),        B=(b,b),        C=(c,c)=ABA,           (SCB8)
```

and `AB=((1 2 3),(1 2 3))` has order three.  Consequently the stabilized
braid authenticates neither fine factor as identity on the reservoir and
does not cancel the native/external `S_3` holonomy.

This is a scoped reservoir model of the full displayed occurrence table,
not a finite representation of EL20.  A positive three-coordinate word
must use a coefficient sum before the two complementary packets separate,
or impose an additional same-carrier relation identifying one private
reflection across the two `S_3` factors.  The pure complementary braid in
`(SCB2)` only reproduces the product gauge.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
stabilized-cross-braid-coefficient-proof
