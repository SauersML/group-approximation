---
rg: 2
id: some-artin-twisted-brin-thompson-group-embeds-in-no-fp-group
kind: claim
title: Some Artin group A has a twisted Brin-Thompson group AV_A that embeds in no finitely presented group
distinct_from:
  some-artin-group-has-unsolvable-word-problem: that is the existence of an Artin group with unsolvable word problem; this is the non-embedding statement for its twisted Brin-Thompson group, equivalent to it through self-twisted-bt-group-fp-embedding-iff-solvable-wp.
  every-artin-twisted-brin-thompson-group-embeds-in-fp-group: that is the affirmative answer to Zaremsky Problem 3.8; this is its negation.
---

**OPEN.** There is an Artin group `A` such that the twisted Brin–Thompson group
`AV_A`, for the translation action, embeds in no finitely presented group.

By `self-twisted-bt-group-fp-embedding-iff-solvable-wp` this is equivalent to
`some-artin-group-has-unsolvable-word-problem`. The routes
`artin-twisted-bt-without-fp-host-from-unsolvable-wp` and
`artin-unsolvable-wp-from-twisted-bt-without-fp-host` record both directions.

## Attempts

- **Through an Artin group with unsolvable word problem.** No candidate is known.
  - Every class in the artifact §5 is excluded: right-angled, spherical, irreducible
    euclidean, FC type, large type, dimension ≤ 2 and rank three.
  - Artin groups of rank at most 3 are covered, so a witness has rank at least 4.
    It must contain a spherical triangle, since 2-dimensional groups are excluded,
    and it must be neither FC nor euclidean.
- **Directly, without the word problem.** Impossible in principle: a finitely
  presented host exists as soon as `A` has solvable word problem (Higman). So a proof
  of non-embedding must prove unsolvability.
