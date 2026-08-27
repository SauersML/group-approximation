---
rg: 2
id: hyperlinear-groups-have-factorization-property
kind: claim
title: Every hyperlinear group has Kirchberg's factorization property
distinct_from:
  hyperlinear-implies-sofic: that asks whether Hilbert--Schmidt matrix approximation can be replaced by permutation approximation; this asks whether it can be upgraded to completely positive maps on the full group C*-algebra, and neither is known to imply the other.
  non-hyperlinear-group: that asks for a group without any Hilbert--Schmidt approximation; this asks that every group with one also have the stronger lifting property.
artifacts:
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

Consequence that makes it unlikely as stated: with Kirchberg's theorem that
Kazhdan groups with the factorization property are residually finite (Math.
Ann. 299 (1994)), this claim implies that every hyperlinear Kazhdan group is
residually finite, hence that every infinite simple Kazhdan group --- the
manuscript's `H = EL₁₂(L_{F₂}(1,2))` among them --- is non-hyperlinear.  That
would settle `non-hyperlinear-group`.  So the claim is at least as hard as
producing a non-hyperlinear group, and its failure is the expected answer.

Open.  Carried here because it is the generic route into
`literal-group-factorization-property`.
