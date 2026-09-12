---
rg: 2
id: hyperbolic-rf-question-equals-non-mf-question-proof
kind: route
title: Complete the four-way equivalence conditional on the missing Kazhdan MF obstruction
target: hyperbolic-rf-question-equals-non-mf-question
requires:
  - hyperbolic-rf-vtf-kazhdan-equivalence
  - mf-kazhdan-group-without-finite-quotients-is-trivial
artifacts:
  - research/artifacts/hyperbolic-four-statements-audit-2026-09-11.md
---

This is a valid **conditional** route. Its second prerequisite is open after
the MF-to-weak-quasidiagonality citation audit; the route does not assert
that prerequisite.

The first prerequisite gives (1) iff (2) iff (3). If the second prerequisite
were established, the infinite Kazhdan witness in (3) could not be MF:
otherwise its absence of nontrivial finite quotients would force it to be
trivial. It is already word-hyperbolic, so it would witness (4).

Conversely (4) implies (1). Section 3 of the artifact proves this without
any lifting or stability assumption: for a countable residually finite
group, combine finitely many separating finite quotients and their regular
representations. Their exact unitary matrices define an injective group map
to a norm matrix corona. Hyperbolic groups are countable; hence a non-MF
hyperbolic group is not residually finite.

The missing work is proving the stated Kazhdan MF obstruction, or finding
a different construction from (1) to (4). The verified obstruction to weak
quasidiagonality alone does not discharge that work.
