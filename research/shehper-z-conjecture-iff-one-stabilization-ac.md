---
rg: 2
id: shehper-z-conjecture-iff-one-stabilization-ac
kind: claim
title: Shehper et al.'s presentations-of-Z conjecture on n generators is equivalent to one-stabilization AC-triviality in rank n−1
distinct_from:
  shehper-z-presentations-are-ac-trivial: that is the conjecture itself, which is open; this is the proved equivalence between its rank-n case and a rank-(n−1) statement
  balanced-trivial-presentations-one-stabilization-ac-trivial: that is the open one-stabilization statement; this proves it is the same problem as the conjecture, one rank up
artifacts:
  - research/artifacts/hl-andrews-curtis-status-2026-09-13.md
---

Fix n ≥ 2. The following statements are equivalent.

**(A_n)** Take any presentation ⟨x_1, …, x_n | r_1, …, r_{n−1}⟩ of Z in which each
x_i generates Z, and any word w for which ⟨x_1, …, x_n | r_1, …, r_{n−1}, w⟩ presents
the trivial group. Then that presentation is AC-trivial. This is Conjecture
`conj:general_Z` of Shehper et al. on n generators, read with the printed
hypothesis that the presentation is of the trivial group.

**(B_{n−1})** For every balanced presentation ⟨y_1, …, y_{n−1} | s_1, …, s_{n−1}⟩ of
the trivial group, the one-stabilization ⟨x, y_1, …, y_{n−1} | x, s_1, …, s_{n−1}⟩ is
AC-trivial.

**Consequences.**
- (A_3) implies that AK(3) is stably AC-trivial, with a single stabilization.
- The full conjecture (A_n for all n) implies
  `balanced-trivial-presentations-one-stabilization-ac-trivial`, and hence
  `stable-andrews-curtis-conjecture`.
- A proof that some rank-2 balanced trivial presentation, e.g. AK(3), is not
  AC-trivial after one stabilization would refute Conjecture `conj:general_Z` on 3
  generators.
