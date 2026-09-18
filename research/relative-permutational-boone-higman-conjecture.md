---
rg: 2
id: relative-permutational-boone-higman-conjecture
kind: claim
title: Every finitely generated group with solvable word problem sharply embeds in a type [A_2] actor modulo its kernel (Fournier-Facio--Wu--Zaremsky Conjecture 1.8)
distinct_from:
  permutational-boone-higman-conjecture: that asks for a FAITHFUL type (A) action of a finitely presented overgroup; this allows a kernel that the input meets trivially, and passing from this to that is FFWZ Question 5.9.
  boone-higman-implies-relative-permutational-bh: that is the proved implication from Boone--Higman to this, group by group; this is the conjecture for all inputs.
  decidable-groups-embed-in-abelian-cofinite-hosts: that is a sufficient embedding statement, via cofinite-abelian-subgroups-give-relative-pbh; this is the conclusion.
---

**OPEN.** This node records FFWZ's conjecture (added by lane bh-invent-02, 2026-09-18).

**Statement.** Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Conjecture 1.8, as recorded
in `boone-higman-implies-relative-permutational-bh`. For `Γ` finitely generated with solvable
word problem, there is a group `G` with a type [A_2] action on a set `S` such that `Γ` sharply
embeds in `(G, ker(G ↷ S))`.

## Known

- **From Boone--Higman.** It follows from Boone--Higman for `Γ` (FFWZ Theorem C,
  `boone-higman-implies-relative-permutational-bh`).
- **Products.** It is closed under finite direct products
  (`relative-pbh-closed-under-finite-direct-products`).
- **Upgrade to PBH.** It gives PBH for `Γ` exactly when the kernel can be removed
  (`a2-kernel-removal-iff-image-satisfies-pbh`, FFWZ Question 5.9).
- **Necessary.** Every group satisfying it has solvable word problem, since type [A_2] kernels
  are co-r.e. (`a2-kernel-removal-forces-recursive-kernel`).
- **Sufficient: abelian-cofinite hosts.** It holds for every subgroup of a finitely presented
  group with a faithful action that has finitely generated stabilizers and a finite-rank free
  abelian subgroup with finitely many orbits (`cofinite-abelian-subgroups-give-relative-pbh`).
  The route is `relative-pbh-via-abelian-cofinite-hosts`.
