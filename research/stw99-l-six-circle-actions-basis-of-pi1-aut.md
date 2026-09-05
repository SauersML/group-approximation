---
rg: 2
id: stw99-l-six-circle-actions-basis-of-pi1-aut
kind: claim
title: Six circle actions are an integral basis of pi_1(Aut) of a UCT Kirchberg algebra with K-theory (Z2,(1,0),Z2)
distinct_from:
  stw99-problem-l-explicit-automorphism-loops: that root asks for loops in Aut of the stably finite rotation algebra A_theta itself; this answers only the Kirchberg alternative STW offer alongside it, and does so through a nonconstructive classification isomorphism, so it leaves the rotation-algebra request untouched.
  stw99-problem-liv-circle-actions-framework: that problem asks for a classification framework for circle actions whose crossed products are stably finite; this uses circle actions merely as convenient representatives of homotopy classes and classifies nothing about the actions themselves.
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

Let `A = B (x) B` as above, a unital UCT Kirchberg algebra with scaled
graded K-theory `(Z^2, (1,0), Z^2)`.  Fix once a unital classification
isomorphism `psi : C -> A` with

```text
e_C |-> e,   b |-> beta,   [U_1] |-> x,   [U_2] |-> y
```

and set `sigma_j(z) = psi h_j(z) psi^{-1}` for `j = 1,...,4`.  Then the
six loops

```text
sigma_1, sigma_2, sigma_3, sigma_4, rho_1, rho_2
```

are all CIRCLE ACTIONS and their classes are a `Z`-basis of
`pi_1(Aut(A), id) = Z^6`.  In the coordinates

```text
( (Delta x)_e, (Delta x)_beta, (Delta y)_e, (Delta y)_beta, (Delta beta)_x, (Delta beta)_y )
```

their columns are

```text
     [ 1 0 0 0  1  0 ]
     [ 0 1 0 0  0  0 ]
L =  [ 0 0 1 0  0  1 ] ,      det L = 1.
     [ 0 0 0 1  0  0 ]
     [ 0 0 0 0  0 -1 ]
     [ 0 0 0 0  1  0 ]
```

The coordinates of an arbitrary class `(a,b,c,d,f,g)` in this basis are
`(a-g, b, c+f, d, g, -f)`.

Generation does not depend on the marking: for ANY fixed unital
isomorphism `psi`, the four transported graph loops span the intrinsic
submodule `Hom(K_1(A), K_0(A))` and the two tensor actions project onto a
basis of `Hom(K_0(A)/Z[1_A], K_1(A))`.  Nothing here assumes the six
actions commute.
