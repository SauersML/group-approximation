---
rg: 2
id: atlas-full-large-no-simple-quotient-under-million
kind: claim
title: The full large rectangle has no nonabelian simple quotient below one million
artifacts:
  - experiments/atlas_a4_full_large_all_simple_under_million.g
  - research/artifacts/atlas-a4-full-large-all-simple-under-million.json
distinct_from:
  atlas-full-large-rectangle-has-no-screened-small-simple-quotient: that tests nine selected simple groups; this exhausts every possible simple target below one million using the forced order divisor.
  atlas-full-large-finite-escape-has-simple-local-factor: that produces a constrained simple composition factor from a faithful finite carrier; this supplies the exhaustive finite-simple computation needed to bound that factor.
---

The universal full-large rectangle has no nonabelian finite simple quotient of
order less than `10^6`.

This is exhaustive, not an Atlas sample.  Every nonabelian simple quotient has
order divisible by `360`, because its marked `A5`, `S3 x S3`, and `S4`
vertices inject.  GAP's complete
`AllSmallNonabelianSimpleGroups([1..999999])` catalogue contains exactly
sixteen groups with that divisibility.  Exact `GQuotients` computations give
zero epimorphism classes for every one.

Consequently any faithful finite carrier for the full-large support has a
nonabelian simple composition factor of order at least one million.

