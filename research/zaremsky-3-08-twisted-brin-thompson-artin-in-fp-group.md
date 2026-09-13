---
rg: 2
id: zaremsky-3-08-twisted-brin-thompson-artin-in-fp-group
kind: claim
title: "Zaremsky Problem 3.8 resolved: does the twisted Brin-Thompson group AV_A of every Artin group A embed in a finitely presented group?"
root: true
distinct_from:
  artin-groups-satisfy-boone-higman: that asks for a finitely presented SIMPLE envelope of an Artin group that already has solvable word problem; this asks only for a finitely presented host of the simple group AV_A, which by self-twisted-bt-group-fp-embedding-iff-solvable-wp exists exactly when A has solvable word problem.
artifacts:
  - research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3, Problem 8, verbatim:
"Given an Artin group A, we can embed it in the finitely generated simple twisted
Brin–Thompson group AV_A. Does this group embed in a finitely presented group? If
so, then this would prove that Artin groups have solvable word problem."

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-08-by-yes` requires
  `every-artin-twisted-brin-thompson-group-embeds-in-fp-group`.
- **No**: `zaremsky-3-08-by-no` requires
  `some-artin-twisted-brin-thompson-group-embeds-in-no-fp-group`.

Never write a `requires: []` route into this claim.

**Reading.**
- `A = A_Γ` is an Artin group on a finite nonempty set of standard generators.
- `AV_A` is the twisted Brin–Thompson group `SV_G` of Belk–Zaremsky
  (arXiv:2001.04579) with `G = S = A` and `A` acting on itself by left translation.
  This is the group written `G·V_G` in Belk–Bleak–Matucci–Zaremsky (arXiv:2306.16356,
  §4).
- `AV_A` is finitely generated and simple, and `A` embeds in it (BBMZ Theorem 4.13).
- The question is read for every Artin group: yes means every `AV_A` has a finitely
  presented host.

**The question is the word problem for Artin groups.** By
`self-twisted-bt-group-fp-embedding-iff-solvable-wp` (BBMZ Corollary 4.14 together
with Higman's embedding theorem), for each `A`, `AV_A` embeds in a finitely presented
group iff `A` has solvable word problem. Zaremsky's second sentence is the forward
direction, and Higman's theorem gives the converse. So:

- yes ⇔ `every-artin-group-has-solvable-word-problem`. This is Charney's *Problems
  related to Artin groups*, Problem 10, open per BBMZ footnote 10.
- no ⇔ `some-artin-group-has-unsolvable-word-problem`.

**Partial answer.** `AV_A` embeds in a finitely presented group whenever `A` is
right-angled, spherical, irreducible euclidean, of type FC, of large type,
2-dimensional or of rank three, or a finite direct product of such groups, because
those word problems are solvable. See the artifact §5; it is landing as
`known-type-artin-twisted-bt-groups-embed-in-fp-groups`.

**AV_A is never its own host.** The translation action of an infinite group has
infinitely many orbits of two-element subsets, so by Zaremsky's criterion
(arXiv:2405.18354, `twisted-brin-thompson-finite-presentation-criterion`) `AV_A` is
not finitely presented. See the artifact §4; it is landing as
`self-twisted-bt-group-of-infinite-group-is-not-fp`.

## Attempts

- 2026-09-13, z3-08-artin-bt-embed:
  - Reduced both answers to the word problem for Artin groups, and answered yes for
    every class with a known word-problem algorithm.
  - What remains is Charney's Problem 10.
  - A proof strategy through explicit hosts is in the artifact §6 (Lemma 3,
    unreviewed): an Artin group inside a type (A) actor with a free orbit gives
    `AV_A ≤ TV_Δ`, finitely presented and simple.
- Credit: the equivalence is BBMZ Corollary 4.14 combined with Higman's embedding
  theorem. This graph adds only that it settles the logical status of Problem 3.8.
  Unreviewed.
