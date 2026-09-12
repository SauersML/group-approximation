---
rg: 2
id: artin-groups-satisfy-boone-higman
kind: claim
root: true
title: Every Artin group with solvable word problem embeds in a finitely presented simple group
distinct_from:
  boone-higman-conjecture: that quantifies over every finitely generated group with solvable word problem; this only over Artin groups with solvable word problem, a named special case that the conjecture implies.
  fp-residually-finite-boone-higman: that is item (12) of the same survey problem, over finitely presented residually finite groups; this is item (13), over Artin groups, which are finitely presented but are not known to be residually finite in general.
  spherical-artin-boone-higman-reduces-to-e6-e7-e8: that is an established conditional reduction of the permutational form for spherical types to three exceptional types; this is the open problem over all Artin groups.
  aut-free-groups-satisfy-permutational-boone-higman: that imports the Aut(F_n) theorem and the Artin types it reaches (A, B = C, D, I_2(m), Ã); this is the open problem over all Artin groups.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**OPEN.** Every Artin group with solvable word problem embeds in a finitely
presented simple group.

This is item (13) of Problem 5.3 in Belk--Bleak--Matucci--Zaremsky,
*Progress around the Boone--Higman Conjecture*, arXiv:2306.16356v3: "Prove the
Boone--Higman conjecture for: ... (13) Artin groups with solvable word problem."
Their footnote 10 notes that solvability of the word problem is itself open for
general Artin groups, and known for right-angled, spherical and Euclidean types.

It is a root because it is a named open problem in its own right. It is a
special case of `boone-higman-conjecture`.

## What is known

Per the attached artifact:
- **Permutational form (PBH):**
  - types A_n, B_n = C_n, D_n, I_2(m) and Ã_n, by BFFHZ Corollary B, imported in
    `aut-free-groups-satisfy-permutational-boone-higman`;
  - the Euclidean triangle types Ã_2, C̃_2, G̃_2, by BLIW Corollary 12.8 and
    Remark 12.7;
  - every C̃_n, `c-tilde-artin-groups-satisfy-permutational-boone-higman`.
- **Boone--Higman:** right-angled Artin groups, by survey Theorem 5.1(3).
- **Stated open** (BFFHZ, survey Remark 5.4): the exceptional spherical types,
  and the Euclidean types other than Ã_n and the triangle cases.

## Attempts

1. **Subgroups of braid and mapping class groups.**
   - *Works* for A, B, D, I_2(m), Ã (BFFHZ) and for C̃_n: Allcock's
     twice-punctured plane, followed by the Fadell--Neuwirth fibration into
     B_(n+2).
   - *Dies for B̃_n and D̃_n as it stands.* Allcock realizes them only inside
     braid groups of orbifolds with cone points of order 2. A braid around a
     cone point has finite order, so the punctured-plane argument does not
     apply.
   - *Dies for E_6, E_7, E_8.* Paris, §7.1: the Perron--Vannier geometric
     monodromy is faithful only for types A and D.
2. **Linearity.** Spherical types are linear over `Q(x,y)`: Paris, Corollary 6.5,
   together with Crisp's embedding into products of A, D, E factors.
   - *Stops* at the open root `char-zero-linear-groups-satisfy-boone-higman`,
     transcendence degree 2. Zaremsky's `GL_n(Q)` theorem does not reach it.
3. **Groups acting on locally finite trees** (BLIW Theorem C over F_2).
   - *Works* for the Euclidean triangles, through Squier's finite-index
     splittings.
   - *Stops* for the large-type triangles. Jankiewicz's splittings
     F_3 ∗_(F_7) F_4 have edge group of index 2 in F_4, but finite index in F_3
     is recorded only for (3,3,3).
4. **Decidable-edge HNN permanence.** The Jankiewicz splittings over finite-rank
   free groups reduce the admissibly oriented 2-dimensional Artin groups to
   `bh-embeddability-survives-decidable-edge-hnn`, which is open.
