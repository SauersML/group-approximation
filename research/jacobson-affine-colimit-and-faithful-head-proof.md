---
rg: 2
id: jacobson-affine-colimit-and-faithful-head-proof
kind: route
title: Identify the affine finite-group colimit and transfer the complete literal kernel
target: jacobson-coherent-quotient-is-faithful-and-has-mf-dichotomy
requires:
  - jacobson-coherent-quotient-has-four-word-gap-criterion
  - jacobson-shift-literal-quotient-is-laurent-times-z
  - jacobson-shift-head-generates-normal-finitary-kernel
  - jacobson-shift-head-dies-in-amenable-targets
artifacts:
  - research/artifacts/jacobson-coherent-quotient-is-the-faithful-literal-group-2026-09-08.md
---

The artifact checks both universal maps between the coherent quotient
and the triangle of three complete `GL_3(F_2)` groups along their
prescribed `GL_2(F_2)` subgroups. Allcock, Corollary 2, identifies this
colimit with the simply connected affine group of type `A_tilde_2`
over `F_2`. The central kernel of its standard map to the Laurent
special linear group is `F_2^x={1}`, by the loop-group description in
Capdeboscq--Kirkina--Rumynin, Section 6, page 31. The root coordinates
are checked explicitly, so the resulting map is the specified `kappa`.

The isomorphism `ker(pi)~=ker(kappa)` respects conjugation. The image
of the normal closure of `E` is the normal closure of `e`, proving
the former is the whole literal kernel. Simplicity of `L` and its
trivial literal centralizer then make every head-retaining homomorphism
faithful. Evaluation in finite fields proves residual finiteness of the
symbol quotient, yielding the MF radical dichotomy and the claimed
interpretation of the four-word infimum.

The primary source statements, all small-field hypotheses and exact
root embeddings are recorded in the artifact. These are algebraic
presentation inputs; no infinite-group spectral theorem is invoked.
