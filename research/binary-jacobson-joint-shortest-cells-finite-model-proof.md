---
rg: 2
id: binary-jacobson-joint-shortest-cells-finite-model-proof
kind: route
title: Place the finite packet and balanced involution in the marked LEF Whitehead shift subgroup
target: binary-jacobson-joint-shortest-cells-have-a-finite-marked-model
requires:
  - binary-jacobson-finitary-whitehead-shift-is-marked-lef
  - binary-jacobson-one-step-finite-type-envelope-is-marked-mf
  - binary-jacobson-first-mixed-kernel-is-three-syllable
  - binary-jacobson-shortest-affine-braid-is-finite-marked
---

Let `L` be the finitary general linear kernel in the literal binary Jacobson
group and let `a` be the balanced Whitehead translation from the first
prerequisite.  Every element of

```text
F=GL_3(F_2[Q]) ~= GL_3(F_2) x GL_3(F_2)
```

differs from the identity on only the finite head/tail coordinate packet, so
`F<=L`.  The constant Weyl element `w_12` also lies in `L`, and the defining
factorization of the balanced involution is

```text
h=a w_12.                                                (1)
```

Therefore

```text
<F,h> <= <L,a>=H.                                       (2)
```

The first prerequisite proves that `H` is LEF and that its literal head root
`w=x_13(Q)` is nonidentity.

We use the standard finite-presentation consequence of LEF.  Let
`<X | R>` be any finite presentation whose generators are interpreted in a
LEF group, whose finitely many relators hold there, and whose marked word is
nonidentity.  Form a finite subset containing `1`, the interpreted
generators, every successive prefix of every relator and of the marked word,
and all products needed to pass from one prefix to the next.  An injective
partial homomorphism of this table into a finite group assigns values to `X`
which satisfy every relator exactly.  It therefore extends to a homomorphism
from `<X | R>`, and injectivity on the marked prefixes keeps the marked word
nonidentity.

Apply this observation inside `(2)` to a finite presentation of the finite
overlap amalgam `Gamma_F`, augmented by the two relators `(JFM1)`.  Both
relations hold for the literal Jacobson elements by the cited prerequisites.
The resulting finite homomorphism retains `w`, proving the claim.  The same
argument applies verbatim to any further finite relation list whose literal
values stay inside `<F,h>`.
