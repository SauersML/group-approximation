---
rg: 2
id: mixed-completeness-braid-retains-s3-square-gauge
kind: claim
title: The mixed completeness braid retains an independent S3 spectator gauge
artifacts:
  - research/mixed-completeness-braid-gauge-proof.md
distinct_from:
  stabilized-cross-braid-has-s3-square-gauge-fence: that factorizes each cross Whitehead through a third coordinate and then fuses complementary branch packets; this puts the completeness sum inside one aggregate braid whose first two factors contain literal factors of `K_0`.
  aggregate-cross-commutator-sum-has-finite-s6-gauge: that forms `pr+rp=1` in a four-coordinate commutator and returns an external root; this forms `pr+q_1=1` in a three-coordinate Coxeter braid and compares its gauge directly with the literal `K_0=UVU` subword.
---

**ESTABLISHED MIXED-BRAID FENCE.**  On coordinates `(7,8,9)`, put

```text
U=x_78(p),       V=x_87(r),
U'=x_79(1),      V'=x_97(q_1),
A=UU',           B=VV'.                                  (MCB1)
```

Thus `U,V` are literal factors of

```text
K_0=UVU.                                                (MCB2)
```

If `A=1+X` and `B=1+Y`, direct multiplication gives

```text
X=pE_78+E_79,       Y=rE_87+q_1E_97,
X^2=Y^2=0,
XY=(pr+q_1)E_77=E_77,
YX=q_1E_88+rE_89+q_1E_99.                              (MCB3)
```

In particular `XYX=X` and `YXY=Y`, so the literal aggregate words obey

```text
A^2=B^2=1,             ABA=BAB.                        (MCB4)
```

This braid genuinely uses completeness before the two arms are separated:
its forward product is `pr+q_1=q_0+q_1=1`.  It also contains the actual
cross-channel Steinberg occurrence

```text
[V,U']=x_89(r),                                         (MCB5)
```

while `[U,V']=1` because `q_1p=0`.

Nevertheless the complete displayed occurrence table has an exact finite
reservoir gauge model.  In `S_3 times S_3`, take the standard adjacent
reflections `a,b` and `c=aba=bab`, and set

```text
u=(a,1),       v=(b,1),
u'=(1,a),      v'=(1,b).                               (MCB6)
```

Then the literal `K_0` subword has gauge

```text
uvu=(c,1),                                             (MCB7)
```

whereas the aggregate actors and their braid output have gauges

```text
alpha=uu'=(a,a),
beta=vv'=(b,b),
alpha beta alpha=beta alpha beta=(c,c).                (MCB8)
```

The cross output in `(MCB5)` may carry the identity reservoir factor,
because `v` and `u'` lie in separate factors; the nontrivial Leavitt label
is still the literal matrix coefficient `r`.  All row/column commutations
and the mixed zero row are exact.  Thus the aggregate braid output differs
from the native `K_0` gauge by the independent spectator `(1,c)`.  The
coefficient identity in `(MCB3)` does not identify or cancel that spectator.

This is a scoped reservoir model of the displayed ordinary occurrence
table, not a finite representation of EL20.  A useful continuation must
return the channel-nine spectator to an already typed native occurrence;
the mixed braid alone does not close the ESB selector attachment.

Restoring the positive signed-Hecke occurrence `U'=x_79(1)` does not make
the relative aggregate output into the missing bridge.  The exact
calculation `mixed-braid-gauge-cancellation-misses-signed-hecke-targets`
shows that the comparison word with `K_0` contains a nonconstant
`x_29(r)` term and transports neither `Q` nor `J_1QJ_1^(-1)`.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
mixed-completeness-braid-gauge-proof
