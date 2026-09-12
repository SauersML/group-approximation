---
rg: 2
id: magnus-moldavanskii-hierarchy-with-decidable-edges
kind: claim
title: Magnus subgroups of one-relator groups are free with decidable membership, and exponent-sum-zero letters split the group as a Magnus-subgroup HNN extension
distinct_from:
  one-relator-groups-are-coherent: that is the Jaikin-Zapirain--Linton theorem that finitely generated subgroups of one-relator groups are finitely presented; this is the classical package of the Freiheitssatz, Magnus's solution of the generalized word problem and the Magnus--Moldavanskii hierarchy, and has no coherence content.
  simple-envelope-forces-solvable-word-problem: that derives a solvable word problem from a finitely presented simple envelope; this supplies decidable membership in Magnus subgroups for every one-relator group directly, by Magnus's induction, with no envelope.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `G = <A | r>` with `A` finite and `r`
cyclically reduced. A **Magnus subgroup** is a subgroup `<A_0>` with
`A_0 ⊆ A`.

1. **Freiheitssatz** (Magnus 1930). If `r` involves every letter of `A` and
   `A_0 ⊊ A`, then `<A_0>` is free with basis `A_0`. Letters that do not occur
   in `r` split off as a free factor, so for arbitrary `A`: if `A_0` omits some
   letter occurring in `r`, then `<A_0>` is free with basis `A_0`.
2. **Generalized word problem** (Magnus 1932). For every `A_0 ⊆ A` there is an
   algorithm deciding, for a word `w` in `A^±`, whether `w ∈ <A_0>`. With
   `A_0 = ∅` this is the word problem, so every one-relator group has solvable
   word problem.
3. **HNN form** (McCool--Schupp 1973, Theorem 1). If a letter `t` occurring in
   `r` has exponent sum zero in `r`, then `G` is an HNN extension, with stable
   letter `t`, of a one-relator group whose associated subgroups are Magnus
   subgroups.
4. **Moldavanskii embedding** (1967). Every one-relator group
   `G_1 = <A_1 | r_1>` embeds in a one-relator group `G_1'` that is an HNN
   extension of a one-relator group `G_2 = <A_2 | r_2>` with Magnus associated
   subgroups and `|r_2| < |r_1|`.

## Verification

Read on 2026-09-12 from M. Linton and C.-F. Nyberg-Brodda, *The theory of
one-relator groups: history and recent progress*, arXiv:2501.18306, extracted
on MSI (`/scratch.global/sauer354/orbh-lit/2501.18306.txt`):
- item 1 is its Theorem 1.3.1, with the free-factor remark that follows it;
- item 2 is Theorem 1.3.6 and §1.3.3: "the generalized word problem asks for
  deciding membership in Magnus subgroups of one-relator groups", and "This
  solves the generalized word problem in all one-relator groups";
- item 3 is the first paragraph of §1.5.4, citing McCool--Schupp;
- item 4 is its Theorem 1.5.8.

The verbatim wording is in the linked artifact. The original papers of Magnus,
Moldavanskii and McCool--Schupp were not read. Consumers that need the precise
shape of the hierarchy (lengths, omitted letters, the shift isomorphism) rederive
it from items 1 and 3 by Tietze moves, as
`magnus-hnn-permanence-forces-one-relator-bh-proof` does.
