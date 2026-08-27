---
rg: 2
id: complementary-q-child-one-arm-split-proof
kind: route
title: Track the a1 and b1 returns through the complementary cylinder labels
target: one-arm-return-of-complementary-q-child-stays-orthogonal
requires:
  - native-b1-completeness-factorization-stays-projective-times-c2
  - finite-prefix-labelled-windows-remain-projective
---

The coefficient products are

```text
q a_1=a_1,           p a_1=0,
b_1q=b_1,            b_1p=0,                          (1)
a_1b_1=q,            b_1a_1=p.                        (2)
```

Applying the ordinary composable-root commutator law to `(1)` proves
`(QAR2)--(QAR3)`.  This also proves minimality: a nonzero commutator with the
fixed root `Q` requires one composable root, and `U` or `V` is already one
such root.

For the finite image, retain the old ten projective summands

```text
q@1,q@2,q@3,q@4,q@5,q@6,
p@7,e_2@8,e_3@9,p@10.                                 (3)
```

They carry the literal projective `SL_10(F_2)` head.  The three additional
summands

```text
p@2,q@7,q@10                                           (4)
```

are pairwise orthogonal to the summands of `(3)` at every repeated ambient
coordinate.  On `(4)`, the coefficients in `(QAR2)` are exactly the binary
matrix units

```text
Q : q@10 -> q@7,
U : p@2  -> q@10,
V : q@7  -> p@2.                                      (5)
```

Thus `Q,U` or `Q,V` generate the standard `UT_3(F_2)` positive-root group.
With all three arrows, `(2)` supplies the remaining root positions and the
elementary image is `SL_3(F_2)`, of order `168`.

Every cross product between a matrix unit on `(3)` and one on `(4)` is zero:
different ambient coordinates give the matrix-coordinate zero, while a
repeated coordinate gives one of

```text
pq=qp=0,
t_1s_0=t_0s_1=0.                                     (6)
```

Therefore the two elementary-image factors commute and intersect trivially,
proving `(QAR5)`.  Composing the Steinberg packet with this finite elementary
image avoids any assertion about opposite-root elements in the Steinberg
kernel.

Finally the natural `SL_10` profile has marked and star ranks `256` and `64`
and kills the full-Hecke signed average.  Tensoring with the `168`-dimensional
regular representation of the complementary `SL_3` factor gives `(QAR6)`.
All displayed nonzero elementary roots remain nonidentity in that tensor
product representation.
