---
rg: 2
id: rainone-non-almost-unperforated-minimal-outer-action-exists
kind: claim
title: Some minimal properly outer action on a C*-algebra satisfying the hypotheses of Rainone's Theorem 4.22 has a type semigroup that is not almost unperforated (Rainone's page-33 question)
distinct_from:
  free-minimal-cantor-action-with-finite-clopen-type: that asks for a free action, ideally of F_2, with a finite clopen class; this is Rainone's general question, for any minimal properly outer action satisfying his hypotheses.
  rainone-type-semigroup-crossed-product-dichotomy: that records Rainone's theorems; this is his question whether their almost-unperforation hypothesis can fail.
---

**Question (Rainone, *Finiteness and paradoxical decompositions in
C\*-dynamical systems*, arXiv:1502.06153, page 33, verbatim).**  "It is
unknown to the author if there are examples of minimal and properly outer
actions on C*-algebras satisfying the conditions in Theorem 4.22 for which the
type semigroup is not almost unperforated. In particular, is there a free and
action of the free group F_2 on the Cantor set X for which S(X, F_2, C) is not
almost unperforated? Although Ara and Exel construct actions of a finitely
generated free group on the Cantor set for which the type semigroup is not
almost unperforated, these actions are not minimal [1]. Moreover, almost
unperforation may be too strong a condition to establish (5) ⇒ (1) in Theorem
4.21. What is required is that every 'infinite element' (in the sense that
(k+1)x ≤ kx for some k) is properly infinite."

**Claim.**  Some action as in the first sentence exists: `A = C(X)` for a
Cantor space `X`, with a minimal, topologically free (equivalently properly
outer) action, whose type semigroup is not almost unperforated.  Two stronger
statements hold for the same examples.
* The weaker condition of his last sentence also fails: some element with
  `(k+1)x <= kx` is not properly infinite.
* `S` has no nontrivial state and is not purely infinite.  So the implication
  (5) => (1) of his Theorem 4.21 fails without almost unperforation.

**Status (2026-09-13): established, unreviewed**, by the route
`rainone-question-answered-by-generic-witnesses`, for topologically free
actions of `F_infinity`.  The particular question, a *free* action of `F_2`,
is open: `free-minimal-cantor-action-with-finite-clopen-type`.  Whether his
(5) => (3) fails as well, i.e. whether the crossed product can be traceless
without being purely infinite, is
`cantor-crossed-product-with-finite-type-is-mixed`.
