---
rg: 2
id: hyperlinear-nonsofic-group
kind: claim
title: "Pestov Question 3.4: produce a hyperlinear non-sofic group"
distinct_from:
  non-hyperlinear-group: that claim denies hyperlinearity outright; this one demands a group that IS hyperlinear yet fails soficity — the Q3.4 separation
---

The negative (separation) answer to Question 3.4 — one of the two admissible
routes into the program goal `q3-4-resolved`, alongside its negation
hyperlinear-implies-sofic. Soficity implies hyperlinearity
(sofic-implies-hyperlinear, formalized); the converse is Question 3.4
and is open.

Logical caution (notes/OBSTRUCTIONS.md §5): evidence that a candidate is
*not* hyperlinear does not push Q3.4 toward "yes" — only the flexible side
is informative about Q3.4 at all. Since every known nonsofic group comes
from the same (T)-compression mechanism, Q3.4 may be inaccessible until a
second nonsoficity mechanism exists.

**Status of that caution as of 2026-08-14 (literature scout).** It still
holds literally: nonsofic groups now exist unconditionally, but every one of
them — `openai-leavitt-unit-nonsofic` first, then `kun-thom-nonsofic-wreath`
and Fournier-Facio's torsion-free example (arXiv:2608.02025), both of which
build on it — is the same pattern, namely one-sided compression `t Gamma t^(-1) <= Gamma` plus
property (T) plus a commuting non-LEF subgroup. Two qualifications:

- A candidate second mechanism now exists in the literature, conditionally:
  `nonsofic-hyperbolic-group`, via Chapman--Peled (arXiv:2509.21566), whose
  engine is the local testability of expander codes rather than expander
  decomposition of sofic approximations. It is conditional on an unproved
  probabilistic estimate and has produced no group.
- The separation problem itself is no longer untouched: `weakly-sofic-not-sofic`
  is now settled, by composing the Kun--Thom wreath with Glebsky's
  residually-finite-by-weakly-sofic permanence. That is the same shape as
  Q3.4 with a different approximation class, and it isolates what the
  hyperlinear side is missing — a permanence theorem with no hypothesis on
  the coset action.

**Status 2026-08-26 (abstract-embedding pass and notebook ingestion).**
Hyperlinearity of any candidate is equivalent to an abstract unitary
embedding (`abstract-unitary-embedding-upgrades-to-hyperlinear`), but for
compressed Kazhdan pairs that freedom is bounded: the Kazhdan subgroup is
always represented non-amenably (`amenable-kazhdan-models-absorb-compression`),
every model splits into an atomic corner (never faithful), a regular-character
corner (the setting of all routes above) and a remainder carrying
compression-fixed mixtures of infinite-index induced characters that are
non-regular on every root subgroup
(`kt-remainder-corner-characters-are-infinite-index-induced`,
`remainder-corner-root-character-is-persistently-nonregular`).  The nonsofic
Kun--Thom double now decides one of the two roots either way
(`kt-pair-group-double-is-not-hyperlinear` versus
`kt-double-mixed-word-trace-selection`).  Two routes were added into this
claim from the attack notebook
(`research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md`):
`hyperlinear-nonsofic-from-leavitt-retention`, whose single open leaf
`leavitt-presentation-double-positive-rank-retention` is a norm-to-trace
transfer for Shulman pairs of the simple Kazhdan quotient
`EL_4(L_(F_2)(1,2))` with the defect necessarily on the Kazhdan generators
(`intertwiner-retention-is-equivalent-to-hyperlinearity`), and
`hyperlinear-nonsofic-from-free-lamp-hnn` through the open
`kt-free-lamp-hnn-group-is-hyperlinear`.
