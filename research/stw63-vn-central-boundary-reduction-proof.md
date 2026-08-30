---
rg: 2
id: stw63-vn-central-boundary-reduction-proof
kind: route
title: Remove the established finite, type-III, atomic and separably acting central pieces
target: stw63-remaining-vn-boundary-is-semifinite-nonsep
requires:
  - stw63-arbitrary-type3-vn-asymptotic-uniqueness
  - stw63-arbitrary-type1-factor-uniqueness
  - stw63-atomic-type1-vn-uniqueness
  - stw63-product-sigmafinite-type2inf-uniqueness
  - stw63-semifinite-von-neumann-codomains-have-uniqueness
  - stw63-all-vn-rank-and-ideal-data-collapse
---

Use the canonical central type decomposition of a von Neumann algebra.  The
finite part is covered without countability by center-valued-trace
uniqueness.  The entire type-III part is covered, with arbitrary center and
cardinality, by strongly-purely-infinite full-map classification.  Arbitrary
type-I factors and their atomic products are covered by Hadwin's cardinal
rank theorem.  Li--Hadwin--Liu's factor-specific Corollary 1 covers every
sigma-finite type-II-infinity factor without a separable-predual hypothesis;
product closure covers arbitrary products of these.  The existing general
semifinite theorem covers every separably acting remaining piece.

Unitary equivalence assembles over a finite central direct sum simply by
taking the direct sum of the implementing unitaries.  Therefore only the
nonseparably acting properly infinite semifinite pieces outside the atomic
and separably acting cases can remain.  The global rank-and-ideal theorem
already erases those invariants on these pieces, leaving exactly the stated
rank-to-norm implication as the unresolved step.  No direct-integral model
or measurable selection beyond its valid standard-Borel scope is assumed.
