---
rg: 2
id: hyperbolic-rf-vtf-kazhdan-equivalence-proof
kind: route
title: Assemble the Osin filling equivalence and the Kazhdan quotient construction
target: hyperbolic-rf-vtf-kazhdan-equivalence
requires:
  - hyperbolic-rf-question-equals-vtf-question
  - kapovich-wise-rf-iff-finite-quotients
  - olshanskii-g-subgroup-quotient-theorem
  - torsion-free-hyperbolic-kazhdan-partner-exists
artifacts:
  - research/artifacts/hyperbolic-four-statements-audit-2026-09-11.md
  - research/artifacts/hyperbolic-quotientless-kazhdan-proof-2026-09-11.md
---

The filling equivalence gives (1) iff (2), including the case in which a
nonidentity finite-residual element initially has infinite order.

Kapovich--Wise, contrapositively, turns (1) into the existence of a nontrivial
hyperbolic group with no nontrivial finite quotient. Such a group must be
infinite, since a nontrivial finite group maps nontrivially to itself.
Alternatively Sections 1--3 of the quotientless artifact derive this step
from Olshanskii: in a sixfold free product create a free subgroup of the
finite residual, check that it normalizes no nontrivial finite subgroup,
then map it onto a non-elementary hyperbolic quotient.

Section 4 of that artifact kills the maximal finite normal subgroup of the
quotientless witness and takes its free product with a torsion-free
non-elementary hyperbolic Kazhdan partner. Both factors are G-subgroups:
the Bass--Serre tree proves that neither normalizes a nontrivial finite
subgroup. Olshanskii's simultaneous-surjection theorem gives a non-elementary
hyperbolic common quotient. As a quotient of the partner it has property
(T), and as a quotient of the quotientless factor it has no nontrivial
finite quotient. This proves (1) implies (3).

Finally an infinite group with no nontrivial finite quotients is not
residually finite, proving (3) implies (1). No existence premise occurs in
this route's dependencies; it proves only their equivalence.
