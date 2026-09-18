---
rg: 2
id: supersolvable-arrangement-groups-lie-in-the-pbh-class
kind: claim
title: The fundamental group of the complement of every supersolvable (fiber-type) complex hyperplane arrangement lies in B_A and embeds in a finitely presented simple group
distinct_from:
  fiber-type-toric-arrangement-groups-lie-in-the-pbh-class: that is the toric and elliptic case, where every fibre has free fundamental group of rank at least 2; this is the linear case, where rank-one fibres occur and split off as direct factors Z.
  free-kernel-extensions-stay-in-the-permutational-class: that is the permanence lemma; this applies it along Terao's tower of linear fibrations.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `supersolvable-arrangement-groups-lie-in-the-pbh-class-proof`.
This is a lane proof and not independently reviewed. No priority is claimed. Many of
these groups (pure braid groups, pure Artin groups of types A and B, and the pure braid
groups of G(d,1,n)) were already known to be in `B_A`.

**Statement.** Let `A` be a supersolvable arrangement of hyperplanes in `C^ℓ`, central
or affine. Equivalently, by Terao's fibration theorem (1986; cited, not read), `A` is
fiber-type. Then `π_1(C^ℓ − ∪A)` lies in `B_A`. So it embeds in a finitely presented
simple group and has solvable word problem.

**Examples.**
- Graphic arrangements of chordal graphs.
- The reflection arrangements of types A_n, B_n and G(d,1,n), and of rank-2 groups.
- The Hessian arrangement of G_25 is not covered: it is fibred by the Hesse pencil,
  not by a linear projection. Its braid group is covered by
  `complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34` instead.
