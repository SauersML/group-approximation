---
rg: 2
id: kervaire-killing-form-holds-over-nonnegative-deficiency-groups
kind: claim
title: No nontrivial group with a finite presentation of nonnegative deficiency is killed by adjoining one generator and one relator
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that is the injectivity conjecture for every group and every nonzero degree; this is only the killing (nontriviality) form, only over groups with a finite presentation having no more relators than generators.
  kervaire-killing-failure-over-deficiency-zero-group-exists: that is the open existence of a balanced failure; this is its negation, strengthened to cover positive deficiency, which item 1 of the bridge theorem already settles unconditionally.
artifacts:
  - research/artifacts/ideas-bridges-2026-09-13.md
---

**OPEN.** For every nontrivial group `G` with a finite presentation
`<x_1, ..., x_n | r_1, ..., r_m>` with `m <= n`, and every `w in G * <t>`,
`(G * <t>)/<<w>> != 1`.

**Status of the pieces.**
- The case `m < n` is established: item 1 of
  `deficiency-zero-kervaire-failure-yields-whitehead-counterexample`.
- The case `m = n` is the negation of
  `kervaire-killing-failure-over-deficiency-zero-group-exists`.
- The route `nonnegative-deficiency-kervaire-via-finite-whitehead` derives both
  from `whitehead-asphericity-conjecture`.
