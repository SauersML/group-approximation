---
rg: 2
id: fpbs-infinite-contact-zero-relative-cost-proof
kind: route
title: Sample shared connectors and derandomize finite connection tests with paid tails
target: fpbs-infinite-contact-zero-relative-cost
requires:
  - fpbs-cost-one-backbone-fixes-completion-bill
artifacts:
  - research/artifacts/fpbs/docs/shared-component-repair.md
---

Section 1 supplies the direct proof. Each infinite contact has
infinitely many distinct oriented starting vertices, so sparse
independent vertex marking connects it almost surely. Countably
many contacts suffice per orbit. For a finite prefix of H-demands,
choose finitely many successful path tests, approximate their marks
by independent colors of separating measurable partition atoms,
and repair every failure directly. Append all remaining H-maps,
paying their ordinary tail cost. Averaging yields repairs of cost
at most epsilon c(H)+eta for arbitrary positive epsilon and eta.

Sections 3--4 prove the two audited subsidiary assertions. A finite
cut vector is orthogonal to the finite cycle space and hence lies
in the kernel of a dominated positive cycle contraction; the
determinantal inclusion formula makes deleting the whole cut a
null event. For the recursive parallel-path graph, every cut crosses
infinitely many edge-disjoint detours, while the exact series-parallel
percolation recurrence stays at most one half at p=one quarter.
Every connecting path has finite depth, justifying passage to the
union. Imported for the cut audit: the defining determinantal
inclusion probabilities from Lyons, linked in the artifact.

These are written deductions, not formal proof verification.

For Section 6, import BLPS Theorem 13.7 and the standard uniform-
forest expected-degree and domination identities at the linked
primary sources. Use the known commuting-family fixed-price-one
case F_2 x Z. Its free forest-times-Bernoulli action and infinite
forest subrelation both have cost one, so the required completion-
bill formula yields zero relative cost, despite the independent
sprinkling obstruction. No universality is inferred from this case.

Section 7 gives an explicit dependent repair on a larger space:
rare full vertical columns intersect rare full horizontal layers,
and every infinite forest tree has an infinite projection onto at
least one coordinate. Independent marks on that coordinate make
the tree hit the connected helper almost surely. Countability
handles all trees. The direct cost count is delta+2 eta. The
nontrivial invariant column event prevents copying this helper law
into a Bernoulli action, whose Z-restriction is ergodic.
