---
rg: 2
id: compilers-cannot-drop-decidability-proof
kind: route
title: Run the type (A) corollary backwards through both compiler constructions
target: compilers-cannot-drop-the-decidability-hypothesis
requires: [mallery-zaremsky-shift-similar-envelope, fp-strongly-shift-similar-admits-type-a-action, type-a-action-gives-boone-higman-for-subgroups, fiber-product-conjugation-action-lemma, one-two-three-fibre-product-theorem, conjugacy-finite-recursive-presentation-solvable-wp, novikov-boone-fp-group-undecidable-word-problem]
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Proof written out in the target node.  Every prerequisite is used:

* Mallery--Zaremsky and Proposition 5.3 give part (a)'s type (A) action;
* the fiber-product lemma and the 1-2-3 theorem give part (b)'s;
* Corollary B is the backwards step in both, and is the only source of the
  word "solvable" in either;
* the conjugacy-class enumeration discharges the `N = T` instance of (b)
  without any of the above, which is what the target node's third section
  asserts;
* Novikov--Boone is what makes the two conclusions non-vacuous -- without a
  finitely presented group with unsolvable word problem, both "hence" clauses
  would be statements about an empty class and the claim would say nothing
  about what a proof must contain.

No Lean counterpart exists.
