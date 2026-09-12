---
rg: 2
id: c-tilde-artin-groups-satisfy-permutational-boone-higman
kind: claim
title: Every Euclidean Artin group of type C̃_n embeds in B_(n+2), satisfies permutational Boone--Higman, and embeds in a finitely presented simple group
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that imports BFFHZ Theorem A and the Artin types of its Corollary B (A, B = C, D, I_2(m), Ã); this adds the Euclidean type C̃_n, which BFFHZ list as open for n >= 3.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports BLIW families, and the survey credits the same paper with the Euclidean triangle Artin groups, which include C̃_2; this covers C̃_n in every rank, through braid groups rather than locally finite trees.
  spherical-artin-boone-higman-reduces-to-e6-e7-e8: that is a conditional reduction for spherical types; this is an unconditional theorem for one Euclidean family.
  artin-groups-satisfy-boone-higman: that is the open named problem over all Artin groups; this settles the single Euclidean family C̃_n.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**ESTABLISHED.** For every `n >= 1`:
- the Artin group `A(C̃_n)` embeds in the braid group `B_(n+2)`;
- it lies in the permutational Boone--Higman class, i.e. it embeds in a group
  with an action of type (A);
- it embeds in a finitely presented simple group, a twisted Brin--Thompson
  group.

**Why it matters.** It closes a case of Problem 5.3(13) in arXiv:2306.16356v3
that the two most recent sources list as open.
- BFFHZ, arXiv:2503.21882v2, after Corollary B: Boone--Higman "remains open for
  the exceptional type spherical Artin groups, and the Euclidean Artin groups
  other than type ~An; in rank 3 it is also known for type ~C2 and ~G2".
- Survey Remark 5.4 keeps open "those of Euclidean type other than the ~An and
  triangle cases (~C2 and ~G2)".
- So both list C̃_n as open for every `n >= 3`.

**Credit and scope.**
- **The embedding is known.** R. Charney and J. Crisp, *Automorphism groups of
  some affine and finite type Artin groups*, arXiv:math/0408412v1 (2004), p. 2,
  read from the PDF extracted on MSI: "It is less well-known (see [1]) that the
  Artin groups A(Bn) and A(~Cn−1), respectively, are isomorphic to the subgroups
  of the braid group A(An) leaving fixed one, respectively two, of the punctures
  in the disk". Since A(A_n) = B_(n+1), this is `A(C̃_n) <= B_(n+2)`.
- The route re-derives it from Allcock's identification
  (`c-tilde-artin-groups-are-punctured-plane-braid-groups`) by the
  Fadell--Neuwirth fibration.
- The permutational property of braid groups is BFFHZ's.
- **What this adds** is only drawing the consequence, which the two sources
  above do not record. The novelty search for that consequence was bounded: an
  arXiv abstract search for "Boone-Higman" through arXiv:2609.01868 on
  2026-09-12, plus the statements above. No priority is claimed for any
  ingredient.
- Types B̃_n and D̃_n are not covered. Allcock realizes them only in braid
  groups of orbifolds with cone points (see `artin-groups-satisfy-boone-higman`,
  Attempts).

**Consequence.** By the closure of the class under direct products, free
products and commensurability (`boone-higman-type-a-class-closed-under-finite-extensions`
and BFFHZ Corollary F), the property passes to any Artin group commensurable
with a direct or free product of groups of types A, B, D, I_2(m), Ã, C̃.

The derivation is `c-tilde-artin-pbh-via-braid-group-embedding-proof`.
