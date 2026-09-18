---
rg: 2
id: lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a
kind: claim
title: For m odd, every B_A lamp group wreathed over the vertex cosets PSL_2(Z[1/2m])/PSL_2(Z[1/m]) gives a group in B_A, in particular Z wr_X PSL_2(Z[1/2]) embeds in a finitely presented simple group
distinct_from:
  z-wr-psl2-z-half-embeds-in-fp-self-similar-group: that is the self-similar question printed in arXiv:2609.01868, refuted by z-wr-psl2-z-half-is-not-residually-finite (the group is not residually finite, so lies in no self-similar group); this is the Boone--Higman / permutational form for the same groups, which the printed question was asked in service of.
  wreaths-over-clopen-stabilizer-cosets-lie-in-b-a: that is the general lemma; this is its application to the Möbius action of PSL_2 of S-integers on the 2-adic projective line.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `lamp-wreaths-over-psl2-tree-vertices-proof` (lane proof; not
independently reviewed; no priority claimed, bounded search: the arXiv full-text search
for "Boone-Higman" through 2609.01868 returns no result on these groups).

## Statement

Let `m ≥ 1` be odd, `G = PSL_2(Z[1/(2m)])` and `H = PSL_2(Z[1/m]) ≤ G`, and let
`X = G/H`. For every group `L` in the permutational class `B_A`, the restricted
permutational wreath product `L ≀_X G` lies in `B_A`. If `L` is finitely generated, it
embeds in a finitely presented simple group.

- `H` is the stabilizer in `G` of the standard vertex `[Z_2 ⊕ Z_2]` of the Bruhat–Tits tree
  of `PGL_2(Q_2)`, so `X` is the orbit of that vertex: one type of vertices of the
  3-regular tree. The point stabilizers are infinite and virtually free (for `m = 1`), and
  `G` has infinitely many orbits on pairs of `X` (distance is invariant).
- **The case `m = 1`, `L = Z^d`.** `Z^d ≀_X PSL_2(Z[1/2])` with `X = PSL_2(Z)\PSL_2(Z[1/2])`
  (right cosets; isomorphic as a `G`-set to `G/H`) embeds in a finitely presented simple
  group. For `d = 1` this is the group of Almeida–Dantas–Oliveira-Tosti,
  arXiv:2609.01868v1. Its introduction (TeX l.221–225) says that it is covered neither by
  their Theorem C, nor by Zaremsky, nor by Belk–Matucci. The authors then ask whether it
  embeds in a finitely presented self-similar group
  (`z-wr-psl2-z-half-embeds-in-fp-self-similar-group`). That has a negative answer: the group
  is not residually finite, so it lies in no self-similar group
  (`z-wr-psl2-z-half-is-not-residually-finite`, lane bh-free-46). So only hosts that are not residually finite can contain it. Here the host is the
  twisted Brin–Thompson group of the type (A) wreath actor built over the clopen action of
  `V_2(Γ_2(1))`, which is finitely presented and simple.
- It is the second test case of `pbh-closed-under-decidable-permutational-wreaths`.
- `L` may be any group in `B_A`, for example any finitely generated linear group in
  characteristic zero (`char-zero-linear-groups-satisfy-permutational-boone-higman`).
