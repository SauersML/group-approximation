---
rg: 2
id: stw99-l-four-loop-basis-of-retraction-kernel-proof
kind: route
title: Subtract columns in the abelian pi_1 and transport along a second classification isomorphism
target: stw99-l-four-loop-basis-of-retraction-kernel
requires:
  - stw99-l-six-circle-actions-basis-of-pi1-aut
  - stw99-l-rotation-oinfty-scaled-k-theory
  - stw99-l-unital-kirchberg-phillips-classification
---

*The four columns.*  `pi_1` of a topological group is abelian and
pointwise composition induces its addition, so the classes of
`kappa_1,...,kappa_4` are column 2, column 4, column 5 minus column 1,
and column 6 minus column 3 of `L`.  Those differences are
`(1,0,0,0,0,1)-(1,0,0,0,0,0) = (0,0,0,0,0,1)` and
`(0,0,1,0,-1,0)-(0,0,1,0,0,0) = (0,0,0,0,-1,0)`.

*`chi` exists.*  `A` and `D` are unital UCT Kirchberg algebras with the
same scaled graded K-theory `(Z^2,(1,0),Z^2)`, by the second
prerequisite, so classification supplies a unital `chi` realising the
prescribed marking.  Fix one; again it is not canonical.

*`r` is well defined and split.*  Under the splitting of Lemma 1,
carried across `chi`, the two displayed coordinates of `Delta_alpha` are
`( (Delta x)_e, (Delta y)_e )` -- two of the six coordinates -- so `r` is
a homomorphism, and the transported `sigma_1, sigma_3` (columns 1 and 3
of `L`, which are the first and third standard basis vectors) are a
section.  No external artifact is needed for this: it is a coordinate
projection of the splitting already established.

*Kernel basis.*  `ker r` is the sublattice `a = c = 0`, of rank four with
basis the second, fourth, fifth and sixth coordinate vectors.  The four
`kappa` columns are `(0,1,0,0,0,0)`, `(0,0,0,1,0,0)`, `(0,0,0,0,0,1)`,
`(0,0,0,0,-1,0)`, whose matrix in that basis has determinant
`1 * 1 * det[[0,-1],[1,0]] = 1`.  So they are a basis of `ker r`, and
adjoining the section gives a basis of `pi_1(Aut(D))`.

*Scope.*  This is the transport step, and it consumes classification
twice: once for `psi` inside the prerequisite and once for `chi` here.
The loops are explicit as words in `psi`, `chi` and named edge phases;
neither isomorphism is given by a formula on generators.  No loops in
`Aut(A_theta)` itself are produced -- see
`stw99-problem-l-explicit-automorphism-loops`, which stays open.
