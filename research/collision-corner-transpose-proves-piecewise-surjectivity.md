---
rg: 2
id: collision-corner-transpose-proves-piecewise-surjectivity
kind: route
title: Place a piecewise tuple injection in a finite collision-algebra corner and transpose it
target: relative-equality-piecewise-injections-are-surjective
requires: [finite-collision-operator-algebras-are-stably-finite]
---

Use the faithful tuple representation of the complex collision algebra
D_n from the required claim, and use its |C|-by-|C| matrix algebra to
act on the vector space with basis C x G^n. Diagonal multiplication by
the indicator of X is an idempotent p in this matrix algebra: every
allowed condition belongs to the collision coefficient algebra, and
Boolean combinations are obtained by multiplication and subtraction
from 1.

Refine the finitely many program pieces to a disjoint definable
partition of X. Each branch is a matrix unit between its source and
target control states, times a coordinate translation and its domain
projection. Their finite sum T acts by

    T delta_x = delta_(F(x)) for x in X,
    T delta_x = 0 for x outside X.

Because F maps X to X, T=pTp. Its formal adjoint T* is also in this
corner. There are finitely many translation terms, so its action on
every basis vector is a finite sum. Injectivity gives the exact basis
identity

    T* T = p.

This is an identity in the algebra by faithfulness of the tuple
representation. The corner p M_|C|(D_n) p is directly finite: indeed,
if vu=p in that corner, then (v+1-p)(u+1-p)=1 in the ambient directly
finite ring, so the reverse identity gives uv=p. Apply this to T*,T
to obtain T T*=p.

For y in X outside the image of F, T* delta_y=0, contradicting
T T* delta_y=p delta_y=delta_y. Hence no such y exists and F is onto.
This also covers empty X and finite groups without a separate counting
assumption. It is an algebraic proof of the asserted restriction on
finite programs, not an enumeration of their possible executions.
