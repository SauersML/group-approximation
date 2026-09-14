---
rg: 2
id: corner-matrix-ring-isos-force-flip-conjugacy
kind: claim
title: Subshift crossed-product ring isomorphisms assembled from diagonal-preserving corner maps force flip conjugacy
distinct_from:
  cantor-crossed-product-matrix-ring-iso-forces-soe: that turns an arbitrary isomorphism of matrix rings over these crossed products into strong orbit equivalence; this gives flip conjugacy, but only for isomorphisms built from diagonal-preserving corner maps
  subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity: that reduces Cartan uniqueness to groupoid-model rigidity; this rules out corners, matrix amplifications and towers as a source of counterexamples
---
**Statement.** Let X and Y be infinite minimal subshifts, R_X = LC(X,F_2) ⋊ Z with diagonal D_X, and similarly for Y.
Suppose:
- U ⊆ X and V ⊆ Y are nonempty clopen sets;
- n ≥ 1, with [1_X] = n[1_U] in K^0(X,T) and [1_Y] = n[1_V] in K^0(Y,S);
- φ: e_U R_X e_U → e_V R_Y e_V is a ring isomorphism with φ(e_U D_X) = e_V D_Y.

Then (X,T) and (Y,S) are flip conjugate.

**Consequence.** A decomposition of 1 into n orthogonal idempotents equivalent to e_U gives R_X ≅ M_n(e_U R_X e_U), and
[1_X] = n[1_U] in K_0(R_X) = K^0(X,T). So every ring isomorphism R_X ≅ R_Y of the form M_n(φ) relates only flip
conjugate subshifts, and so does the tower identity R_{X^(k)} ≅ M_k(R_X). Any counterexample to
`subshift-crossed-product-algebraic-cartans-are-conjugate` of the kind asked for there must be non-spatial on every
clopen corner.

Proof route: `corner-matrix-ring-isos-force-flip-conjugacy-proof`.
