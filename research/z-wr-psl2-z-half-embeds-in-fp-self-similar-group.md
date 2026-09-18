---
rg: 2
id: z-wr-psl2-z-half-embeds-in-fp-self-similar-group
kind: claim
title: The permutational wreath product Z wr_X PSL_2(Z[1/2]) over X = PSL_2(Z)\PSL_2(Z[1/2]) embeds in a finitely presented self-similar group
distinct_from:
  pbh-closed-under-permutational-wreaths-with-infinite-stabilizers: that is the general closure of B_A under permutational wreaths with infinite stabilizers (Zaremsky Question 5.7); this is one explicit instance, asked in the self-similar form.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**OPEN.** Printed question of M. R. Almeida, A. C. Dantas, A. S. de Oliveira-Tosti,
*On the self-similarity of permutational wreath products and their embedding into
finitely presented simple groups*, arXiv:2609.01868v1 (TeX main.tex l.226–228):

> Does there exist an embed of Z ≀_X PSL(Z[1/2]) into a finitely presented
> self-similar group?

Here `X = PSL(Z)\PSL(Z[1/2])` (their Theorem, l.150). They note that Cornulier lists
this group as a non-finitely presented residually finite wreath product on which
`PSL(Z[1/2])` acts primitively with finitely generated stabilizers, and that it is
not covered by their Theorem C, by Zaremsky, or by Belk–Matucci (l.221–225). A
positive answer gives Boone–Higman for it via Zaremsky's Theorem 1.1
(arXiv:2405.09722).

**Relation to main.** For Boone–Higman (not self-similarity) this is an instance of
`pbh-closed-under-permutational-wreaths-with-infinite-stabilizers` (OPEN). The top
group `PSL_2(Z[1/2])` is linear, so it lies in a finitely presented self-similar
group by `fg-linear-groups-embed-in-fp-self-similar-groups`; the lamps over the
infinite stabilizer `PSL_2(Z)` are the obstacle.
