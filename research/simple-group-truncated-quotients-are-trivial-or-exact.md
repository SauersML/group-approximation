---
rg: 2
id: simple-group-truncated-quotients-are-trivial-or-exact
kind: claim
title: For a finitely generated infinite simple group, every sufficiently exact marked quotient of a truncated presentation is trivial or exact on a given ball
distinct_from:
  minimal-free-sft-full-group-pattern-models-are-exact: that proves rule groups on validly coloured Z^d-sets reproduce the marked full group, and records the isolation lemma (fp iff isolated); this is the quantitative trivial-or-exact dichotomy for quotients of truncated presentations, which turns any nontrivial finite or linear model into a LEF witness.
---

**ESTABLISHED (unreviewed; folklore, no novelty claimed).**

**Setting.** `Gamma` is finitely generated, infinite and simple, with finite symmetric generating set `S`.
For `n >= 1` let `P_n = <S | words of length <= 2n that are trivial in Gamma>`.

**Theorem.** For every `m` there is `n(m) >= m` such that every marked group `(Q, S)` in which all words
of length `<= 2n(m)` that are trivial in `Gamma` are trivial (equivalently, every marked quotient of
`P_(n(m))`) is either trivial, or has exactly the same relators of length `<= 2m` as `Gamma`, i.e. the
same marked `m`-ball.

**Corollaries.**
1. `Gamma` is LEF iff `P_n` has a nontrivial finite quotient for every `n`.
2. `Gamma` is LEF iff `P_n` has a nontrivial finitely generated linear quotient for every `n`
   (Malcev, `finitely-generated-linear-groups-are-residually-finite`).
3. LEF witnesses can be taken to be finite simple groups: a nontrivial finite quotient of `P_(n(m))`
   has a nontrivial simple quotient, which is again a quotient of `P_(n(m))`.
4. Any nontrivial finite `F(S)`-set on which every trivial word of length `<= 2n(m)` acts trivially
   generates a permutation group that is exact on the `m`-ball of `Gamma`.

**Model test.** `Gamma = Z` is not simple and the dichotomy fails: the finite quotients `Z/N` of
`P_n = Z` are nontrivial and not exact for `N <= 2m`. For a finite simple `Gamma` such as `A_5`, `P_n = Gamma`
for large `n`, and its only quotients are `1` and `Gamma`, as the theorem predicts.

Route: `simple-group-truncated-quotients-are-trivial-or-exact-proof`.
