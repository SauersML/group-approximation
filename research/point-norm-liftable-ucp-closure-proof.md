---
rg: 2
id: point-norm-liftable-ucp-closure-proof
kind: route
title: Apply Arveson closedness of liftable completely positive maps
target: point-norm-approximate-ucp-sections-close-to-exact
requires: []
---

Put `phi_epsilon=pi o s_epsilon`.  Each `phi_epsilon:S->Q` is ucp and
liftable, and `(PN1)` says `phi_epsilon->phi` in point norm.

Arveson's lifting-closure theorem says that, for a separable operator system
(in particular a finite-dimensional one), the collection of liftable
contractive completely positive maps into a fixed quotient is point-norm
closed.  Applied to the net `phi_epsilon`, it gives a contractive completely
positive lift of `phi`.  Since `phi` is unital, the standard unital form of
the lifting theorem replaces that lift by a ucp lift without changing its
quotient.  This proves the claim.

This is the closure input used in the approximation formulation of the LLP;
see Arveson's lifting theorem (Theorem 6 in *Notes on extensions of
C-star-algebras*, 1977) and the streamlined CP-stability/LLP treatment in
T. Sinclair, *CP-stability and the local lifting property*, New York J. Math.
23 (2017), 739--747.
