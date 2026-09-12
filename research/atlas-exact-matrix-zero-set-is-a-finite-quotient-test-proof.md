---
rg: 2
id: atlas-exact-matrix-zero-set-is-a-finite-quotient-test-proof
kind: route
title: Apply Malcev residual finiteness to the finitely generated matrix image
target: atlas-exact-matrix-zero-set-is-a-finite-quotient-test
requires:
  - atlas-a4-finite-quotient-escape-fence
  - exact-finite-dimensional-group-table-classicalizes
  - atlas-root-energy-ellipse-controls-s3-distance
---

Suppose first that an exact matrix model exists.  The two represented chart
copies generate a finitely generated subgroup

```text
Lambda <= U(d) <= GL_d(C).
```

The defining packet and collision relations give a homomorphism
`Gamma_A4 -> Lambda`.  Its restriction to either chart is faithful because a
regular `A8` representation is faithful.  Choose one nonidentity chart
element `g`; its image in `Lambda` is nonidentity.

By Malcev's theorem, the finitely generated linear group `Lambda` is
residually finite.  Hence some homomorphism from `Lambda` to a finite group
does not kill the image of `g`.  Composing with `Gamma_A4 -> Lambda` gives a
nontrivial finite quotient of `Gamma_A4`.

Conversely, let `Gamma_A4 -> F` be a nontrivial finite quotient.  The
trivial/injective dichotomy in `atlas-a4-finite-quotient-escape-fence` says
that both chart restrictions are injective.  In `Reg(F)`, either chart
therefore restricts to `[F:A8] Reg(A8)`, and every defining relator is exactly
one.  This is the required exact matrix model.  The same fence gives its root
ellipse value at least one.

Finally, the displayed `3/128` inequality is the exact-collision specialization
of the already established root-ellipse/S3-distance theorem.  No matrix
dimension enters that argument.  Malcev is used only to classify existence of
an exact finite-dimensional zero, and supplies no uniform conclusion for an
unbounded approximate sequence.

