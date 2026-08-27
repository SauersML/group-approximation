---
rg: 2
id: rank-twelve-leavitt-group-lacks-factorization-property
kind: claim
title: The rank-twelve Leavitt group H has no factorization property, so its canonical trace is not amenable
distinct_from:
  literal-group-factorization-property: that is the open question for the non-Kazhdan literal group E; this is the decided negative for the manuscript's Kazhdan simple group H, decided by Kirchberg's theorem.
  thom-sofic-kazhdan-groups-without-factorization-property: that is Thom's family of sofic Kazhdan non-residually-finite groups; this is the manuscript's own group, which is Kazhdan, simple and infinite, and whose soficity is not claimed.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean
---

Let `H = EL₁₂(L_{F₂}(1,2))` be the manuscript's simple Kazhdan group.  `H` does
not have Kirchberg's factorization property; equivalently (Brown, Theorem
4.1.9) the canonical trace of `C*(H)` is not an amenable trace.

**Established.**  `H` has property (T) (Lean
`RankTwelveEndpoints.hasKazhdanPropertyT`) and is simple and infinite (Lean,
`RankTwelveSimplicity`), so it is not residually finite
(`not_isResiduallyFinite_of_isSimpleGroup_of_infinite`, proved in `GroupApproximation/Manuscript/NinetyNineProblems/FactorizationProperty.lean`);
Kirchberg (Math. Ann. 299 (1994)) shows Kazhdan groups with the factorization
property are residually finite.  Lean:
`NinetyNineProblems.rankTwelveLeavitt_not_hasFactorizationProperty`, with
Kirchberg's theorem as the typed input `KirchbergKazhdanFactorizationInput`.

Why it matters for STW Problem X(1): `C*_r(H)` is the manuscript's separable
stably finite non-MF algebra, but the canonical trace of `C*(H)` is not
amenable, so `H` is not a candidate for an amenable non-quasidiagonal trace.
The candidate is the sofic literal group `E`, whose factorization property is
open.
