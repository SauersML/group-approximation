---
rg: 2
id: s3-packed-root-retraction-audit-proof
kind: route
title: Abelianize the positive-root packet and retain the three endpoint conventions
target: s3-packed-root-has-retractive-finite-escape
requires: []
artifacts:
  - research/artifacts/s3-packed-root-retraction-audit-2026-08-23.md
---

Put `Q=V_b=1`, `Z_X=-1`, and `Z_Y=1`.  Take the target pairs for
`b=00,01,11` to be respectively

```text
(1,1),       (-1,1),       (1,1).
```

The two diagonal products are one and the crossed product is zero, proving
that every residual in `(SEC3)` vanishes.  The source is scalar, so both
source commutators vanish.  Direct subtraction leaves only

```text
D_(00,X)=D_(11,X)=2,
```

which proves `(PRE1)`.  The matrix-unit calculation in
`orthogonal-hecke-row-packs-common-source-energy-into-one-root` then gives
`(PRE2)`.

For the root packet, let `x_12(a)` and `x_23(b)` be translations by `(a,0)`
and `(0,b)` on `F_5^2`, and send the central line `x_13(c)` to the identity.
Translations add exactly and commute, hence

```text
[x_12(a),x_23(b)]=1=x_13(ab)
```

for all 25 pairs.  Nonzero translations have no fixed point, so both input
lines remain nontrivial in the permutation representation while `(PRE3)`
holds.  The displayed order-two and order-three linear maps normalize the
translation plane and satisfy the `S3` relations.  A tensor-factor central
`C2` twist commutes with the whole construction.

Substitution into `(PRE4)` gives `8<=0`, a contradiction.  Finally, for any
extension admitting a root-killing retraction, composing this payload
representation with the retraction sets every root word to one without
changing its row data.  This proves the general retractive statement and
the claimed necessity of a non-retractive kernel-reflection relation.

