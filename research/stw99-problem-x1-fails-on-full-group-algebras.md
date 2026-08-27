---
rg: 2
id: stw99-problem-x1-fails-on-full-group-algebras
kind: claim
title: Some countable group has an amenable canonical trace on C*(G) that is not quasidiagonal
root: true
distinct_from:
  stw99-problem-x1-amenable-traces-quasidiagonal: that is the universal question; this is its negation restricted to the canonical traces of full group C*-algebras, carried as a separate node because both sides have live routes.
  literal-central-mark-corona-invisible: that is the operator-norm corona obstruction for one group; this is the trace-level consequence, which needs in addition that the canonical trace of that group be amenable.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

There is a countable discrete group `G` whose canonical trace `τ_G` on the
full group C\*-algebra `C*(G)` is an amenable trace (Brown, Definition 3.1.1)
but not a quasidiagonal trace (Brown, Definition 3.3.1).

Any such group answers Problem X(1) of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026) in the negative, and by Brown's
Theorem 4.1.9 the amenability clause is the same as Kirchberg's factorization
property for `G`.

The candidate is the repository's literal finitely presented group `E`:
`literal-canonical-trace-hyperlinear-not-quasidiagonal` supplies the second
clause outright, and `literal-group-factorization-property` is the open first
clause.  The route `stw99-x1-fails-via-literal-group` records the composition.

Not every non-MF group is a candidate.  Kirchberg (Math. Ann. 299 (1994))
proved that a group with property (T) and the factorization property is
residually finite; so the manuscript's simple Kazhdan group
`H = EL₁₂(L_{F₂}(1,2))` does **not** have the factorization property, its
canonical trace is not amenable, and it says nothing about this problem.  The
literal group `E` is an HNN-type extension and is not itself Kazhdan, which is
why the question stays open for it.
