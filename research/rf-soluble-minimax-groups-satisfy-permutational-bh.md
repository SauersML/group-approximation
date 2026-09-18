---
rg: 2
id: rf-soluble-minimax-groups-satisfy-permutational-bh
kind: claim
title: Finitely generated residually finite virtually soluble groups of finite rank (the virtually torsion-free soluble minimax groups) lie in the permutational Boone--Higman class
distinct_from:
  fp-metabelian-groups-satisfy-boone-higman: that is the metabelian class, of unbounded rank, reached through Wehrfritz's quasi-linearity; this is soluble groups of any derived length, but of finite rank and residually finite.
  free-solvable-groups-satisfy-permutational-boone-higman: that is free soluble groups, of infinite rank, reached by Magnus embeddings and lamp wreaths; this is the finite-rank soluble class, reached through linearity.
  global-field-soluble-linear-products-satisfy-boone-higman: that assumes a linear embedding over global fields; this assumes only group-theoretic hypotheses (finite rank, residual finiteness) and derives linearity from Pyber--Segal.
  fg-soluble-minimax-groups-satisfy-boone-higman: that is the whole finitely generated soluble minimax class, including the non-residually-finite groups with infinite radicable torsion radical, and is OPEN; this is its residually finite part.
artifacts:
  - research/artifacts/gq-bh-bh-solvable-status.md
---

**ESTABLISHED** by `rf-soluble-minimax-groups-satisfy-permutational-bh-proof`
(lane `bh-solvable`, lane proof; it composes one literature import with a reviewed
node). Not independently reviewed. No priority is claimed: the result is a direct
corollary of Pyber--Segal linearity and the linear-group results on main, and may be
folklore.

## Statement

Let `G` be a finitely generated group that is virtually soluble, residually finite,
and of finite Prüfer rank. Equivalently (Pyber--Segal §3, citing Lennox--Robinson
Ch. 5), `G` is a finitely generated virtually soluble minimax group that is virtually
torsion-free. Then `G` lies in `B_A`, the permutational Boone--Higman class of
`boone-higman-type-a-class-closed-under-finite-extensions`. In particular `G` has
solvable word problem and embeds in a finitely presented simple group.

## Scope

- **Derived length is unrestricted.** Polycyclic groups (linear over `Z`) were already
  covered; this class properly contains them and adds non-polycyclic groups of every
  derived length, such as `BS(1,n)` and Abels' groups. The free soluble groups on main
  have infinite rank and are handled by a different route.
- **Examples.** `BS(1,n)`, Abels' groups `A_p`, every polycyclic-by-finite group, and
  every finitely generated torsion-free soluble group of finite rank that is
  residually finite.
- **Not covered.** Finitely generated soluble minimax groups that are not residually
  finite, i.e. those whose maximal periodic normal subgroup `τ(G)` is infinite. The
  quotient of Abels' group by a cyclic subgroup of its center `Z[1/p]` is one. See
  `fg-soluble-minimax-groups-satisfy-boone-higman` (OPEN).

## Lesson for general BH

For soluble groups, residual finiteness together with finite rank is exactly linearity in
characteristic zero (Pyber–Segal), and quasi-linear groups lie in `B_A`. So the whole
"tame" finite-rank soluble world costs nothing beyond the linear hosts. What remains of
soluble Boone–Higman is precisely the groups that are not quasi-linear. They fail
quasi-linearity by one of two mechanisms:
- **Divisible torsion.** An infinite radicable torsion radical makes the group non-RF. See
  `fg-soluble-minimax-groups-satisfy-boone-higman` and
  `compact-skew-products-cannot-carry-divisible-fiber-subgroups`.
- **Dilating commutators.** A commutator acts by a nontrivial power map on a torsion-free
  abelian section. See `q-difference-lamplighter-is-not-quasi-linear`.

A general soluble theorem needs a host for each mechanism, not a better linearity input.
