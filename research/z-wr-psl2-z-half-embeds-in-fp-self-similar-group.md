---
rg: 2
id: z-wr-psl2-z-half-embeds-in-fp-self-similar-group
kind: claim
title: The permutational wreath product Z wr_X PSL_2(Z[1/2]) over X = PSL_2(Z)\PSL_2(Z[1/2]) embeds in a finitely presented self-similar group
refuted_by:
  - z-wr-psl2-z-half-is-not-residually-finite
distinct_from:
  pbh-closed-under-permutational-wreaths-with-infinite-stabilizers: that is the general closure of B_A under permutational wreaths with infinite stabilizers (Zaremsky Question 5.7); this is one explicit instance, asked in the self-similar form.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**REFUTED** by `z-wr-psl2-z-half-is-not-residually-finite` (2026-09-18, lane proof, elementary, not reviewed). The wreath product is not residually finite: `PSL_2(Z)` maps onto every finite quotient of `PSL_2(Z[1/2])`, so all lamps become equal in every finite quotient. Hence it embeds in no self-similar group at all, and the printed question has a negative answer. The original text is kept below as the record.

Printed question of M. R. Almeida, A. C. Dantas, A. S. de Oliveira-Tosti,
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

**Relation to main.** The Boone–Higman form is now settled:
`lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a` (2026-09-18) puts `Z^d ≀_X PSL_2(Z[1/2])` in
`B_A`, so it embeds in a finitely presented simple group. The host there is the
Röver–Nekrashevych group `V_2(Γ_2(1))`, whose commutator subgroup is finitely presented and
simple. It is not a self-similar group containing the wreath product.

**What remains for the printed question.** The top group `PSL_2(Z[1/2])` is linear, so it lies
in a finitely presented self-similar group by `fg-linear-groups-embed-in-fp-self-similar-groups`.
The lamps over the infinite stabilizer `PSL_2(Z)` are the obstacle. A self-similar host would
have to realize the permutation module `Z[X]` inside a self-similar group.
