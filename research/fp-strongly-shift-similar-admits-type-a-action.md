---
rg: 2
id: fp-strongly-shift-similar-admits-type-a-action
kind: claim
title: Every finitely presented strongly shift-similar group admits a type (A) action, hence has solvable word problem
distinct_from:
  mallery-zaremsky-shift-similar-envelope: that is the universal embedding construction and produces a finitely GENERATED strongly shift-similar group; this is the payoff theorem and hypothesizes finite PRESENTATION, which the construction does not supply. The gap between the two is the open claim shift-higman-compiler.
  type-a-action-gives-boone-higman-for-subgroups: that is the general corollary saying what a type (A) action buys; this says that one particular class of permutation groups HAS such an action, and is the only supply of type (A) actions the shift-similar lane owns.
  twisted-brin-thompson-finite-presentation-criterion: that is the equivalence characterizing finite presentability of twisted Brin-Thompson groups; this verifies the four clauses of that equivalence for the natural action of a strongly shift-similar group on the naturals, and is an application rather than a criterion.
  simple-envelope-forces-solvable-word-problem: that derives decidability from a finitely presented simple envelope; this derives decidability from finite presentation plus a self-similarity property of a permutation group, with no simple group in the hypotheses.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Every finitely presented, strongly shift-similar `G <= Sym(N)` admits an
action of type (A) -- so by `type-a-action-gives-boone-higman-for-subgroups`
every subgroup of `G` has solvable word problem and embeds in a finitely
presented simple group.

**Verification status.**  Read from source 2026-08-24.  Zaremsky,
arXiv:2405.18354, Proposition 5.3, verbatim: "Every finitely presented,
strongly shift-similar group admits an action of type (A), and so in
particular has solvable word problem and satisfies the (permutational)
Boone--Higman conjecture."

The action is the natural one on `N`.  The source's two verifications are
that such a group contains `Sym_fin(N)`, which forces finitely many orbits of
two-element subsets, and that the maps `psi_j` identify the point stabilizers
as finitely generated.

## The clause that does the work is finite presentation

Every hypothesis except finite presentation is available for free from
`mallery-zaremsky-shift-similar-envelope`.  So this proposition converts the
whole Boone--Higman conjecture into a single question about presentations of
one explicit family of permutation groups; that conversion is
`boone-higman-via-shift-higman-compiler`, and the question is
`shift-higman-compiler`.

It also runs backwards, and that is not optional bookkeeping: since a
finitely presented strongly shift-similar group has solvable word problem and
so does each of its subgroups, no group in that family can contain a
finitely generated group with unsolvable word problem.  That is what
`compilers-cannot-drop-the-decidability-hypothesis` records, and it is why
the compiler statement must carry a decidability hypothesis rather than
quantify over all finitely presented inputs.
