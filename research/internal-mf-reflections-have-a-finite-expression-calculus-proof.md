---
rg: 2
id: internal-mf-reflections-have-a-finite-expression-calculus-proof
kind: route
title: Induct over finite product-wreath expressions and preserve every factorization invariant
target: internal-mf-reflections-have-a-finite-expression-calculus
requires:
  - leavitt-unit-internal-all-virtually-free-reflections
  - virtually-free-reflections-share-all-residuals
  - finite-product-lift-of-internal-mf-reflections
  - finite-wreath-lift-of-internal-mf-reflection
---

Proceed by induction on a finite expression for `Q`.

At a virtually free leaf, use the internal wandering-corner reflection and
its simultaneous-residual theorem.  At a finite product node, apply the
finite-product lift.  At a finite wreath node, apply the finite-wreath lift.
Every step stays inside `U`, preserves the Hom factorization, and pulls back
the complete MF semantic-closure operator.  This proves `(FEC1)--(FEC4)`.

Residual finiteness is preserved by finite products and by finite extensions;
hence every group in `C` is residually finite.  Its finite quotients detect
every nonidentity visible element and embed as permutation matrices over
every field.  Together with the inherited target-factorization bijections,
this identifies all the stated residuals with `ker(pi_Q)` and proves `(FEC5)`.

Finite generation is preserved by finite products and finite wreathing.
At a product node, coordinate normal generators normally generate the product
kernel.  At a wreath node, the finite actor permutes the coordinate kernels;
for a regular wreath action one coordinate generating set reaches every
coordinate.  Induction gives the final normal-generation statement.
