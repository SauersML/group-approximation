---
rg: 2
id: finitely-presented-nonsofic-from-oai-table-cover
kind: route
title: Cover the first nonsofic group by its own failed finite table
target: finitely-presented-nonsofic-group-exists
requires: [openai-leavitt-unit-nonsofic]
artifacts:
  - c1168433:official/reasoning.tex
  - GroupApproximation/Covers/TableCover.lean
---

## Why sufficient

A second decomposition of the same target, recording that the chapter reaches
it too, by the construction this repository formalizes as
`Covers/TableCover`.

The prerequisite gives a finitely generated group `G` that is not sofic, so
some finite test `(F, epsilon)` fails.  Put `T = {1} cup F cup F^2` and form

    H_F = < X_a (a in T) | X_1 = 1, X_(gh) = X_g X_h (g, h in F) >,

a finite presentation.  Evaluation `X_a -> a` preserves the nontrivial tested
elements.  If `H_F` were sofic, its defining relations would hand back exactly
the approximation of `F` at tolerance `epsilon` that `G` was shown not to
admit; so `H_F` is not sofic.  Enlarging `F` to contain a generating set of
`G` makes the evaluation surjective, so `H_F` is also infinite.

## Relation to the route already there

[[finitely-presented-nonsofic-group-exists]] is already established through
`finitely-presented-nonsofic-group-exists-proof`, from this repository's own
finitely generated witness, and that route is the kernel-checked one.  This
route changes nothing about its status; it is here because the two arguments
are the same construction applied to two different groups, and because the
graph should record that the chapter itself does not stop at a finitely
generated example.

Note that the finite-table cover is generic: it consumes only "finitely
generated and not sofic", so it never distinguishes between witnesses.  A
finitely presented nonsofic group with a *named* structure -- torsion-free, or
hyperbolic, or hyperlinear -- is a different problem, and Fournier-Facio's
torsion-free example (arXiv:2608.02025) is the first case of it settled.
