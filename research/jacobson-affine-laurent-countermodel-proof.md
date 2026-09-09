---
rg: 2
id: jacobson-affine-laurent-countermodel-proof
kind: route
title: Translate the second finite packet and verify the full Laurent affine presentation
target: jacobson-laurent-kernel-surjects-natural-affine-module
requires:
  - jacobson-shift-literal-quotient-is-laurent-times-z
  - jacobson-coherence-defect-is-an-orthogonal-translation
artifacts:
  - research/artifacts/jacobson-laurent-cover-has-a-noncentral-affine-quotient-2026-09-08.md
---

Represent the first finite packet by its constant linear action
on `R^3`. Represent the second by conjugating its entire constant
linear action with `tau_(e_2) diag(z,1,z)`. This conjugation fixes
the whole common `GL_2(F_2)` on coordinates `1,3`, so all finite
relations and all overlap equations hold.

The explicit affine images of `u,h u h,h r h` verify the mixed
commutator. The three translates in the `h q` braid sum to zero.
The coherence word maps to translation by `z e_1`. Its conjugates
under the surjective linear image generate all of `R^3`: applying
`x_21(f)` and subtracting the original vector gives `f z e_2`,
and `z` is invertible. This proves surjectivity and the exact image
of `ker(kappa)`. Commuting with `k=x_31` gives translation by
`z e_3`, witnessing noncentrality.

Evaluation at `z=1` produces the complete eight-point finite
model. The established kernel comparison and boundary word
identity lift the nontriviality and noncentrality conclusions
to `E` in `Gamma`. Only explicit affine algebra and the displayed
prerequisites are used; no infinite-group spectral estimate enters.
