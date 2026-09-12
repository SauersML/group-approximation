---
rg: 2
id: gromov-weiss-monomial-rank-implication-proof
kind: route
title: Failing monomial tuples assemble into a monomial rank ultraproduct, which is a Hamming ultraproduct, so a sofic group would realize the datum
target: gromov-weiss-is-the-monomial-case-of-the-rank-implication
requires:
  - monomial-rank-models-are-hamming-models
  - sofic-groups-are-surjunctive
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

## Why sufficient

Artifact Section 2, Theorem 2.1.
- **Assembly.** If the implication fails for every reverse word, the amplified direct sums of Theorem 1.2 are
  monomial, and their ultraproduct realizes the datum in a monomial rank ultraproduct.
- **Hamming comparison.** Monomial rank distance and Hamming distance on `F^x × {1, ..., N}` agree up to a factor
  two, so the monomial rank ultraproduct embeds in a Hamming ultraproduct of finite symmetric groups.
- **Contradiction.** The realizing group is countable and sofic, hence surjunctive, while realizing a strict datum
  makes it not surjunctive.
