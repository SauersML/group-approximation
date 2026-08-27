---
rg: 2
id: hyperlinear-groups-have-factorization-property
kind: claim
title: Every hyperlinear group has Kirchberg's factorization property
refuted_by: [thom-sofic-kazhdan-groups-without-factorization-property]
distinct_from:
  hyperlinear-implies-sofic: that asks whether Hilbert--Schmidt matrix approximation can be replaced by permutation approximation; this asks whether it can be upgraded to completely positive maps on the full group C*-algebra, and neither is known to imply the other.
  non-hyperlinear-group: that asks for a group without any Hilbert--Schmidt approximation; this asks that every group with one also have the stronger lifting property.
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

For every countable discrete group `Γ` with `L(Γ)` embeddable in `R^ω`, the
canonical trace on `C*(Γ)` is amenable, i.e. `Γ` has Kirchberg's
factorization property.

Known: residually finite groups and, more generally, maximally almost periodic
groups have the factorization property (Brown, Proposition 4.1.4 and
Corollary 4.1.5); amenable groups do (nuclearity); free groups do because
`C*(F_n)` has the lifting property.  The converse direction (factorization
property implies hyperlinear) is Brown's Theorem 3.1.7(2).

**Refuted (Thom, 2008).**  A. Thom, *Examples of hyperlinear groups without
factorization property*, Groups Geom. Dyn. 4 (2010), arXiv:0810.2180, constructs
groups that are locally embeddable into finite groups --- so initially
subamenable, sofic, hyperlinear --- and have Kazhdan's property (T) without
being residually finite; by Kirchberg's theorem (Math. Ann. 299 (1994), Kazhdan
plus factorization property implies residually finite) they lack the
factorization property.  So hyperlinear, and even sofic, does not imply the
factorization property, and the generic route
`literal-fp-via-hyperlinear-groups-have-fp` is dead.

The same argument shows why the claim was never plausible: it would make every
infinite simple Kazhdan group --- the manuscript's `H = EL₁₂(L_{F₂}(1,2))` among
them --- non-hyperlinear, i.e. it would settle `non-hyperlinear-group`.

Carried as a refuted node so that the generic route into
`literal-group-factorization-property` displays as dead rather than open.

Lean: `NinetyNineProblems.not_forall_hyperlinear_hasFactorizationProperty` (`GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean`).
