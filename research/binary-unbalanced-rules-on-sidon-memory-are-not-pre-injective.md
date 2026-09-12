---
rg: 2
id: binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective
kind: claim
title: A binary automaton whose rule is unbalanced and whose memory quotients are distinct has an invisible single-site flip, over every group
distinct_from:
  free-memory-injectivity-forces-universal-bijectivity: that makes an encoder that is injective over the free group on its memory letters bijective everywhere; this needs only that the quotients m^-1 m' are distinct in the given group, uses no surjunctive cover, and rules out pre-injectivity with an explicit flip.
  unbalanced-effective-rule-certifies-strictness: that turns distinct memory letters, a sufficient forward table and an unbalanced rule into strictness; this shows that for binary rules a sufficient forward table must also force a coincidence among the quotients m^-1 m'.
artifacts:
  - research/artifacts/small-memory-balance-census-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `binary-unbalanced-sidon-memory-proof`.

Let `G` be a group, `M` a finite subset of `G`, `mu : {0,1}^M -> {0,1}` an unbalanced rule, and
`tau(x)(g) = mu((x(g m))_(m in M))`. Call `M` **Sidon in `G`** if the elements `m^-1 m'` with
`m != m'` are distinct for distinct ordered pairs.

**Theorem.** If `M` is Sidon in `G`, then `tau` is not pre-injective, so it is not injective.

**Consequence.** Take a binary injective automaton with an unbalanced rule. Its memory elements
satisfy a relation `m^-1 m' = n^-1 n'` with `(m, m') != (n, n')`, which has length at most four.
In a design this relation must hold in the table group even when the memory letters are distinct.

**Boundary.** For three or more symbols the argument fails: the blind pairs of different
coordinates need not agree (artifact, Remark 3.4).

Artifact, Section 3.
