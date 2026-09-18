---
rg: 2
id: drutu-sapir-group-satisfies-boone-higman
kind: claim
title: The Druţu--Sapir group <a,b | a^2 b^2 a^-2 b^-1> embeds in a finitely presented simple group
distinct_from:
  one-relator-groups-satisfy-boone-higman: that is Boone--Higman for every one-relator group; this is one torsion-free, residually finite, non-linear one-relator test case that no imported theorem reaches.
  virtually-free-by-cyclic-groups-satisfy-boone-higman: that settles virtually free-by-cyclic inputs; this group contains BS(1,2), so it is not one of them.
  fp-residually-finite-boone-higman: that is Boone--Higman for all finitely presented residually finite groups; this is one residually finite one-relator input.
---

**ESTABLISHED (2026-09-13)** through `drutu-sapir-bh-via-power-map-mapping-tori`.
Not independently reviewed. `DS = <a, b | a^2 b^2 a^-2 b^-1>` embeds in a finitely
presented simple group. It even lies in the permutational class `B_A`, as a member
of `power-map-free-mapping-tori-satisfy-permutational-boone-higman`.

**What makes it a test case:**
- **Genuine input.** It is a one-relator group, so it has solvable word problem
  (Magnus; Linton--Nyberg-Brodda, Theorem 1.3.6).
- **Structure.** It is torsion-free and an ascending HNN extension of `F_2`, with
  `DS ≅ (Z[1/2] * Z[1/2]) ⋊ Z` and `BS(1,2) <= DS`. These are the claims in
  `drutu-sapir-group-index-two-squaring-mapping-torus`.
- **Residually finite and not linear.** Linton--Nyberg-Brodda, p. 27, quoted there,
  report this for [DS05]. The primary source was not read.

**What the imported theorems do not reach:**
- **Hyperbolic** (`hyperbolic-groups-satisfy-boone-higman`): `DS` contains `BS(1,2)`.
- **Linear, either characteristic** (`char-zero-linear-groups-satisfy-boone-higman`,
  `char-p-linear-groups-satisfy-permutational-boone-higman`): `DS` is not linear
  [DS05].
- **Virtually finitely generated free-by-cyclic**
  (`virtually-free-by-cyclic-groups-satisfy-boone-higman`): excluded by
  `virtually-free-by-cyclic-groups-contain-no-bs-one-n`.

So among one-relator groups, the residual of `one-relator-groups-satisfy-boone-higman`
contains a residually finite group, not only non-residually-finite ones such as
the Baumslag--Gersten group.

## Attempts

1. **Tree methods (Bux--Llosa Isenrich--Wu, Theorem B).** *Die as stated.*
   - **HNN splitting (DS0):** the base `F(x,y)` has associated subgroup
     `ψ(F_2) = <y^2, x>` of infinite index, so the Bass--Serre tree is not locally
     finite.
   - **Amalgam splitting (K2), for `K`:** the edge group `<c>` has infinite index
     in `BS(1,2)`, so again the tree is not locally finite.
   - **Semidirect form (K4):** the action on a line is not faithful, since `N` acts
     trivially, and `N` is not finitely presented.
   - **Not decided:** whether some other splitting of `DS` meets the hypotheses of
     Theorem B.
2. **Affine or linear hosts.** *Die.* Affine actions on `Z_p` realize `BS(1,2)`
   self-similarly, but their images are metabelian, so no such action of `DS` is
   faithful. Any faithful linear host is excluded by [DS05].
3. **Other directions (superseded 2026-09-13).**
   - A faithful self-similar action of `DS` or of `K` on a regular rooted tree,
     which is consistent with residual finiteness. That would give Boone--Higman via
     `fp-self-similar-groups-embed-in-fp-simple-groups`. It is still unknown whether
     such an action exists.
   - A type (A) actor containing `DS`: supplied by attempt 4.
   - Permanence of `B_A` under ascending HNN extensions of free groups: proved for
     partial-conjugation mapping tori (`pbh-class-closed-under-relative-holomorphs`).
4. **Relative automorphisms (2026-09-13).** *Succeeds.* Let `B = BS(1,2) = <u, σ>`.
   The index-two subgroup `K` embeds in `Aut_B(B * F_2) × Z`:
   - both squaring relations become conjugation by `σ` of the free letters;
   - the free product structure comes from left multiplication by `u` and by a
     conjugate of `u` under a second letter.

   `Aut_B(B * F_2)` lies in `B_A` by
   `pbh-passes-to-relative-free-group-automorphisms`, and `B_A` passes to the
   index-two overgroup `DS`. Details are in `pbh-relative-holomorph-closure-proof`,
   `power-map-free-mapping-tori-pbh-proof` and
   `drutu-sapir-bh-via-power-map-mapping-tori`.

## Update (bh-free-05, 2026-09-18)

Second route: `drutu-sapir-bh-via-ascending-hnn-of-free-groups` derives this claim from `ascending-hnn-of-free-groups-satisfy-boone-higman` (b6bb206cf), since DS is an ascending HNN extension of F_2.
