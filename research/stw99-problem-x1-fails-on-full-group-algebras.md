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
  - GroupApproximation/Sofic/ResidualFinitePacket.lean
  - GroupApproximation/Analysis/QuasiRegularCompression.lean
  - GroupApproximation/Analysis/AmenableTraceGeneratorDense.lean
  - GroupApproximation/Analysis/LocallyRFByIntFactorization.lean
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemXGroups.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**ESTABLISHED, unconditionally and formalized in Lean.**  Take the literal
finitely presented group `E`.  Its maximal canonical trace is amenable by the
locally-RF-by-`Z` theorem `literal-fp-via-folner-rf-core` and is not
quasidiagonal by `literal-canonical-trace-hyperlinear-not-quasidiagonal`.

There is a countable discrete group `G` whose canonical trace `τ_G` on the
full group C\*-algebra `C*(G)` is an amenable trace (Brown, Definition 3.1.1)
but not a quasidiagonal trace (Brown, Definition 3.3.1).

Any such group answers Problem X(1) of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026) in the negative, and by Brown's
Theorem 4.1.9 the amenability clause is the same as Kirchberg's factorization
property for `G`.

The witness is the repository's literal finitely presented group `E`:
`literal-canonical-trace-hyperlinear-not-quasidiagonal` supplies the second
clause outright, and `literal-group-factorization-property` supplies the
first clause by explicit u.c.p. finite-window models.  The route
`stw99-x1-fails-via-literal-group` records the composition.

Not every non-MF group is a candidate.  Kirchberg (Math. Ann. 299 (1994))
proved that a group with property (T) and the factorization property is
residually finite; so the manuscript's simple Kazhdan group
`H = EL₁₂(L_{F₂}(1,2))` does **not** have the factorization property, its
canonical trace is not amenable, and it says nothing about this problem.  The
literal group `E` is an HNN-type extension and is not itself Kazhdan, which is why the Kazhdan obstruction does not apply to it.

Lean endpoint: `NinetyNineProblems.literalFactorizationProperty` proves
amenability of the canonical maximal trace, and
`NinetyNineProblems.not_problemX1Statement` is the axiom-clean unconditional
refutation.  The reusable group-level reading is
`NinetyNineProblems.AmenableCanonicalTraceGroupsAreOperatorMF`
and `amenableCanonicalTraceGroupsAreOperatorMF_of_problemX1`,
`not_problemX1Statement_of_amenable_not_operatorMF` (`GroupApproximation/Manuscript/NinetyNineProblems/ProblemXGroups.lean`): a positive
answer to X(1) makes every factorization-property group operator-MF, so this
claim is equivalent to the existence of a factorization-property group that is
not operator-MF.
