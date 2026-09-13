---
rg: 2
id: rainone-question-boldrini-prasad-citation
kind: route
title: Boldrini-Prasad Theorem 6.10 and Corollary 6.12, with Ara-Bonicke-Bosa-Li Corollary B and Proposition 2.11
target: rainone-non-almost-unperforated-minimal-outer-action-exists
requires: []
---

**Sources.**  Both were read from the arXiv PDFs on 2026-09-13.
* P. Boldrini and A. Prasad, *Topologically free minimal actions without
  dynamical comparison*, arXiv:2607.01896v1 (2 Jul 2026) (BP).
* P. Ara, C. Bönicke, J. Bosa and K. Li, *The type semigroup, comparison and
  almost finiteness for ample groupoids*, arXiv:2001.00376v3 (ABBL).

**Verbatim.**
* BP Theorem 6.10 (p. 23): "Let M be a countable 2-divisible simple refinement
  cone which is not almost unperforated, and u ∈ M be a nonzero element. Let
  (B, μ) be the Fraïssé limit of finite (M, u)-measured Boolean algebras. A
  generic countable subgroup of Aut(B, μ) is dense, isomorphic to F_∞, and acts
  topologically freely on St(B). In particular, there exist topologically free
  minimal actions of F_∞ on the Cantor space without dynamical comparison."
* BP Corollary 6.12 (p. 24): "There exist topologically free minimal actions of
  F_∞ on the Cantor space without invariant measures that fail dynamical
  comparison."  It uses the cone of BP Proposition 3.11: "There exists a
  countable divisible simple refinement cone Q which is not almost unperforated
  and admits no nontrivial states."
* ABBL Corollary B (p. 2): "Let Γ be a countable discrete group acting minimally
  on a locally compact second countable totally disconnected space X. Then the
  transformation group X ⋊ Γ has dynamical comparison if and only if its type
  semigroup S(X ⋊ Γ) is almost unperforated."
* ABBL Proposition 2.11 (p. 14): "Let G be an ample second countable groupoid
  such that every measure in UM(G) is trivial. Then G has dynamical comparison
  if and only if every element in S(G) is properly infinite."

**Deduction.**
* The actions of BP Corollary 6.12 are minimal and topologically free (for
  `C(X)`, this is proper outerness) on the Cantor space, and they fail
  dynamical comparison.  For zero-dimensional `X`, BP's comparison (Remark
  2.17) is the ABBL one (Remark 2.2).
* By ABBL Corollary B, the type semigroup is not almost unperforated.  `C(X)`
  satisfies the hypotheses of Rainone's Theorem 4.22 (Steps 2--3 of
  `rainone-question-answered-by-generic-witnesses`).  So Rainone's first
  question has an example.
* No invariant probability measure exists.  An invariant Radon measure that is
  finite and positive on one clopen set is finite on `X`, by minimality and
  compactness, and normalizes to a probability measure.  So every invariant
  measure is trivial, and ABBL Proposition 2.11 gives an element `x` that is
  not properly infinite.
* With no nontrivial state, Tarski gives `(k+1)x <= kx`.  So Rainone's weaker
  condition fails as well.
* BP do not cite Rainone.  The match with his page-33 question is recorded in
  this graph, not in their paper.
