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

Logical caution (docs/OBSTRUCTIONS.md §5): evidence that a candidate is
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
