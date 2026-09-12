---
rg: 2
id: linear-sofic-rank-implication-per-datum-proof
kind: route
title: Lift realizations in rank ultraproducts to tuples, and assemble failing tuples into a realization by amplified direct sums
target: linear-sofic-surjunctivity-is-a-rank-implication-per-datum
requires:
  - surjunctivity-of-a-local-class-is-reflection-kernel-membership
  - surjunctivity-is-axiomatized-by-rectangle-clauses
  - sofic-implies-linear-sofic-over-every-field
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

## Why sufficient

Artifact Section 1, Theorem 1.2.
- **Kernel versus realization.** The reflection-kernel theorem for the class of `F`-linear sofic groups.
- **Implication forbids realization.** Embed a realizing linear sofic group in a rank ultraproduct and lift the
  generators to tuples. Forward relators have rank `o(n_k)` along `omega`, and the chosen reverse word has rank at
  least `c n_k`. The implication at `eps = c/2` caps it at `c n_k / 2`.
- **Failure gives a realization.** For each reverse word and each `delta = 1/j` take a failing tuple. Equalize
  dimensions by block-diagonal copies and take the direct sum over the finitely many reverse words. Forward
  relators have normalized rank at most `1/j`, and every reverse word keeps normalized rank above
  `eps_w / |W_r|`. The ultraproduct over `j` realizes `D` in a countable subgroup of a rank ultraproduct, which is
  linear sofic by definition.
