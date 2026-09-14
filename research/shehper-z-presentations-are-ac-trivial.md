---
rg: 2
id: shehper-z-presentations-are-ac-trivial
kind: claim
title: Presentations of Z in which every generator generates, completed by a trivializing relator, are AC-trivial
distinct_from:
  z-presentations-with-a-trivializing-relator-are-ac-equivalent: that shows all trivializing completions of one presentation of Z are AC-equivalent; this asserts that they are all AC-trivial
artifacts:
  - research/artifacts/hl-andrews-curtis-status-2026-09-13.md
---

**OPEN.** Conjecture `conj:general_Z` of Shehper et al., arXiv:2408.15332v2
(`sec/stable.tex` l.255–256).

Let ⟨x_1, …, x_n | r_1, …, r_{n−1}⟩ be any presentation of Z where each x_i generates
Z. Then for any word w such that ⟨x_1, …, x_n | r_1, …, r_{n−1}, w⟩ presents the trivial
group, that presentation is AC-trivial.

The printed hypothesis is "exponent sum ±1". Here the node requires instead that
the completed presentation be of the trivial group, which is what the printed
conclusion needs.

The route `one-stabilization-ac-gives-shehper-z-conjecture` derives it from the
one-stabilization statement. By `shehper-z-conjecture-iff-one-stabilization-ac`,
its rank-n case is equivalent to that statement in rank n−1.
