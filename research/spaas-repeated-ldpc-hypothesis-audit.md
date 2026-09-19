---
rg: 2
id: spaas-repeated-ldpc-hypothesis-audit
kind: route
title: Compare chordal graph-product relations and fixed-graph lifting with the repeated-LDPC occurrence quotient
target: spaas-chordal-stability-does-not-cross-the-ldpc-quotient-gate
requires:
  - chordal-abelian-graph-products-hs-stable
  - quadratic-repetition-supports-complete-commutation-overlay
  - sparse-clifford-cycles-refute-average-commutator-rounding
---

Read Spaas's universal graph-product definition literally: distinct vertex
algebras are related only by edge commutation.  The LDPC copy equalities and
parity words are additional quotient relations.  Collapsing them recovers a
fixed finite abelian group but loses the bounded-occurrence average
presentation; retaining them leaves the theorem's category.  Definition 1
is strict same-dimension but fixed-group, and the ultraproduct induction has
no graph-uniform modulus.  The sparse Clifford cycle separates these notions
quantitatively even for the complete chordal family.
