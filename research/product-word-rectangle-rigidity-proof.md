---
rg: 2
id: product-word-rectangle-rigidity-proof
kind: route
title: Three scalar Boolean rectangles force the fourth
target: product-word-stabilizers-cannot-linearize-one-losing-corner
requires: []
---

Let `H_A=H_A^0 directSum H_A^1` and
`H_B=H_B^0 directSum H_B^1`, with all four summands nonzero.  Fix one
product unitary `U=A tensor B` and a phase `lambda`, and suppose `U` is
`lambda I` on the three rectangles

```text
H_A^0 tensor H_B^0,
H_A^0 tensor H_B^1,
H_A^1 tensor H_B^0.                                  (PWR1)
```

We use the elementary tensor lemma: if `S tensor T=lambda I` on
`E tensor F`, where `E,F` are nonzero and `S,T` are invertible, then
`S|_E=alpha I` and `T|_F=beta I` for scalars with
`alpha beta=lambda`.  Indeed, fix nonzero `y in F`.  For every `x in E`,

```text
Sx tensor Ty=lambda x tensor y.
```

Since `Ty` is nonzero, equality of simple tensors forces `Sx` to lie on the
line through `x`.  Applying this to `x`, `x'`, and `x+x'` shows that the
scalar is independent of `x`; the assertion for `T` and the product identity
follow symmetrically.

Apply the lemma first on `H_A^0 tensor H_B^0`.  Write

```text
A|_(H_A^0)=alpha I,   B|_(H_B^0)=beta I,
alpha beta=lambda.                                   (PWR2)
```

The second rectangle in `(PWR1)` and the already fixed nonzero scalar
`alpha` give `B|_(H_B^1)=beta I`.  The third rectangle similarly gives
`A|_(H_A^1)=alpha I`.  Therefore on the remaining rectangle,

```text
(A tensor B)|_(H_A^1 tensor H_B^1)
 =alpha beta I=lambda I.                             (PWR3)
```

The argument applies separately to every member of an arbitrary family of
product-word stabilizers.  Thus no such family can fix all three allowed
Boolean rectangles with the prescribed phases while rejecting only the
fourth rectangle.
