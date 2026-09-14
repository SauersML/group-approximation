---
rg: 2
id: fp-self-similar-groups-embed-in-fp-simple-groups
kind: claim
title: Every finitely presented self-similar group embeds in a finitely presented simple group
distinct_from:
  type-a-action-gives-boone-higman-for-subgroups: that consumes a type (A) permutation action of a finitely presented actor; this consumes a faithful self-similar action on a regular rooted tree and produces the simple group as a Rover--Nekrashevych commutator subgroup, with no permutation-orbit hypothesis in its statement.
  contracting-srn-rational-stabilizers-are-fp: that is a finite-presentation statement about rational point stabilizers in contracting rational similarity groups; this is an embedding theorem whose only hypothesis is finite presentation of the self-similar group itself, with no contraction assumed.
  rover-nekrashevych-simple-groups-are-not-lef-or-torsion-free: that records torsion and non-LEF subgroups inside Rover--Nekrashevych commutators; this is the theorem that such a commutator is a finitely presented simple envelope of the self-similar group.
  boone-higman-thompson-simple-envelope: that gives a computably presented simple envelope for every decidable input; this gives a finitely presented one, but only for finitely presented self-similar inputs, which are residually finite.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**ESTABLISHED (literature import).** Call `G <= Aut(T_d)` *self-similar* when
its image in `S_d wr_d Aut(T_d)` lies in `S_d wr_d G`, i.e. every section of
every element of `G` is again in `G`. Then:

> **Theorem (Zaremsky, arXiv:2405.09722, Theorem 1.1).** Every finitely
> presented self-similar group embeds in a finitely presented simple group,
> and hence satisfies the Boone--Higman conjecture.

The simple group is a commutator subgroup `[V_d(G),V_d(G)]` of the
Rover--Nekrashevych group; the point of the paper is that finite presentation
of `V_d(G)` does not automatically pass to its commutator subgroup. The same
paper's Theorem 1.2 deduces that every finitely generated subgroup of
`GL_n(Q)` satisfies the Boone--Higman conjecture, through self-similar affine
groups `R^n x| GL_n(R)` over suitable rings (its Example 4.7).

Consequently every subgroup of a finitely presented self-similar group
satisfies Boone--Higman. Belk--Bleak--Matucci--Zaremsky, *Progress around the
Boone--Higman conjecture*, Theorem 5.1(12), lists "contracting self-similar
groups and finitely presented self-similar groups" among the known classes.

## Scope

A self-similar group acts faithfully on a locally finite rooted tree, so it
and all of its subgroups are residually finite. This theorem therefore cannot
be a universal route to `boone-higman-conjecture`: an infinite simple input,
which exists for every decidable group by
`boone-higman-thompson-simple-envelope`, is never residually finite. Its
natural target is the residually finite subproblem
`fp-residually-finite-boone-higman`, through
`every-fp-rf-group-embeds-in-fp-self-similar-group`.

DERIVATION
fp-self-similar-groups-embed-in-fp-simple-groups-citation
