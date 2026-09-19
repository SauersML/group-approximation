---
rg: 2
id: stw99-problem-xcii-pure-crossed-products
kind: claim
title: Outer amenable actions on pure algebras give pure crossed products (STW Problem XCII)
root: true
artifacts:
  - research/artifacts/stw99-final-band-cluster-2026-08-30.md
  - research/artifacts/stw99-late-band-audit-2026-08-31.md
---

**Problem XCII of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
For an outer action of a countable discrete amenable group on a unital
simple separable PURE C\*-algebra, when is `A ⋊ G` pure?

## Attempts

* This is the non-nuclear/non-`Z`-stable analogue of XXXVIII.  The two
  independent issues are comparison and almost divisibility for arbitrary
  positive elements of the crossed product.  Automorphism-invariance of the
  divisibility statements inside `Cu(A)` does **not** transfer those
  statements to all of `Cu(A rtimes_r G)`.  Likewise, a simple pure algebra
  can have many traces, and outerness plus amenability does not make the
  crossed product uniquely tracial.  Neither shortcut is used here.

* Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert
  (arXiv:2607.20361, Theorem 9.2) prove relative selflessness of the canonical
  expectation for approximately inner actions of groups with Ozawa's PHP
  property.  This does not give an instance of XCII with a nontrivial acting
  group: PHP groups are C*-simple, while an amenable C*-simple discrete group
  is trivial.  Thus the strongest 2026 crossed-product selflessness theorem
  is transverse to, rather than a solution of, the amenable-action problem.

* A genuine selflessness theorem for strongly outer amenable crossed products
  would imply purity by Gould's 2026 selfless dichotomy, but no such theorem
  is presently available.  Plain outerness is deliberately retained in the
  root because that is the STW question; strengthening it to strong
  outerness would only define a positive subproblem.
