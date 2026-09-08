---
rg: 2
id: fg-central-extension-finite-presentation-proof
kind: route
title: Lift quotient relators to central generators and present the resulting abelian kernel
target: fg-central-extension-of-fp-group-is-fp
requires: []
artifacts:
  - research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md
---

Choose finite generators X of E. A finite presentation of E/C can be
rewritten on the images of X, say <X | r_1,...,r_m>. Let c_i=r_i(X)
in E. Every word representing an element of C is a product of conjugates
of the r_i and their inverses in the free group F(X). In E the c_i are
central, so the conjugates disappear. Thus C=<c_1,...,c_m> as a group.

Let L be the kernel of the surjection Z^m -> C sending the i-th basis
vector to c_i. A subgroup of the finitely generated free abelian group
Z^m is finitely generated; choose a finite generating list V for L.
The group E has the finite presentation on X,c_1,...,c_m consisting of

1. [c_i,c_j]=1 and [c_i,x]=1 for every applicable i,j and x in X;
2. product_i c_i^(v_i)=1 for each v in V;
3. r_i(X)=c_i for each i.

For completeness, the displayed presentation maps onto E. Modulo its
central c_i subgroup it presents E/C exactly. Hence an element of its
kernel is represented by a product of the c_i. Any such product trivial
in E has exponent vector in L and is killed by (2). The map is injective.

Conversely, if E is finitely presented and C has finite generators, add
these generators as relators to present E/C. This proves the equivalence.

This is a standard fact, not a new theorem claimed by this project.
Allcock, *Steinberg groups as amalgams*, printed p. 1841, proof of
Theorem 1.4(i), explicitly uses the upward finite-presentation implication
and refers to Johnson, *Presentations of groups*, Section 10.2:
https://web.ma.utexas.edu/users/allcock/research/steinberg.pdf .
The argument above includes kernel finite generation and a presentation;
no centrality of a Steinberg kernel is used.

