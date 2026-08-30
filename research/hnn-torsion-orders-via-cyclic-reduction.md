---
rg: 2
id: hnn-torsion-orders-via-cyclic-reduction
kind: route
title: Combine cyclic reduction with Britton powers
target: hnn-torsion-orders-equal-base-torsion-orders
requires: [hnn-cyclic-reduction-lemma]
---

Let x in H have finite order. By cyclic reduction, x is conjugate either to
an element of the vertex copy V or to a cyclically reduced word containing a
stable letter. In the second case every positive power is represented by the
literal cyclic concatenation of the reduced word. The seam condition keeps
that concatenation Britton-reduced, so Britton's lemma says no positive power
is the identity. This contradicts finite order. Hence every finite-order
element of H is conjugate into V and its order occurs in Tord(V).

Conversely, the normal-form theorem makes V -> H injective, so a
nonidentity element of V keeps its order in H. Therefore
Tord(H)=Tord(V). QED
