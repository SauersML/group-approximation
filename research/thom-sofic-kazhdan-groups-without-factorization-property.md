---
rg: 2
id: thom-sofic-kazhdan-groups-without-factorization-property
kind: claim
title: There are sofic Kazhdan groups that are not residually finite, hence without Kirchberg's factorization property
invalidates: [literal-fp-via-hyperlinear-groups-have-fp]
distinct_from:
  hyperlinear-groups-have-factorization-property: that is the universal upgrade statement; this is the family of counterexamples that refutes it.
  literal-group-factorization-property: that asks the factorization property for one specific non-Kazhdan group; this is about Kazhdan groups, where Kirchberg's theorem decides the property by residual finiteness.
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

A. Thom, *Examples of hyperlinear groups without factorization property*,
Groups Geom. Dyn. 4 (2010), no. 1, 195--208, arXiv:0810.2180: there is a group
that is locally embeddable into finite groups (hence initially subamenable,
sofic and hyperlinear) and has Kazhdan's property (T) but is not residually
finite.  Kirchberg (Math. Ann. 299 (1994)) proved that Kazhdan groups with the
factorization property are residually finite, so these groups do not have the
factorization property.  Thom also gives a hyperlinear group that is not
initially subamenable, and a group without the factorization property that
embeds in a connected finite-dimensional Lie group; the note answers questions
of Elek--Szabó.

**Established (literature).**  Consequences recorded here: the upgrade
"hyperlinear implies factorization property" is false, so the canonical trace
of a sofic group's full C*-algebra need not be amenable in Brown's sense, and
`literal-group-factorization-property` cannot be reached from
`literal-group-sofic` alone.

Lean: `ThomSoficKazhdanNonResiduallyFiniteInput` (typed literature input) and
`not_forall_sofic_hasFactorizationProperty`,
`not_forall_hyperlinear_hasFactorizationProperty` (`GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean`), which derive the
refutation from that input and Kirchberg's theorem as a typed input.
