---
rg: 2
id: subshift-el-2-simple-modulo-centre-every-finite-field
kind: claim
title: For every infinite minimal subshift X and every finite field F_q, EL_2(LC(X,F_q)⋊Z) modulo its scalar centre is an infinite f.g. simple Kazhdan LEF group
distinct_from:
  subshift-el-2-is-simple-kazhdan-lef: that proves simplicity of EL_2 over F_2 only, through the unit trick LC(X,F_2)^× = {1}; this covers every F_q, replacing the unit trick with e_V u roots, a height-(w+1) tower, SL_d(F_q) and a non-scalar step.
  cyclic-factor-subshift-el-2-is-simple-kazhdan-lef: that covers only subshifts with a finite cyclic factor, by the Morita reduction EL_2(R_X) = EL_2m(R_Y); this covers every infinite minimal subshift, Sturmian ones included, with no matrix-ring structure.
  subshift-elementary-group-is-simple-modulo-centre: that is rank three over every F_q; this is rank two, where the level step runs through the three Peirce blocks of an indicator idempotent instead of the two-sided level ideal.
  root-localization-commutator-is-never-scalar: that excludes the scalar case for root detection with tower subrings B_m(U) and locally constant κ; this is the constant-tower rank-two version, where the margin m = w+1 keeps the top tower level untouched.
artifacts:
  - research/artifacts/sk-el2-fq-all-fields-2026-09-13.md
---

**ESTABLISHED (unreviewed)** by `subshift-el-2-simple-modulo-centre-every-finite-field-proof`.

**Statement.** Let X be an infinite minimal subshift, q a prime power, R = LC(X,F_q) ⋊_T Z and G = EL_2(R).
1. Every normal subgroup of G is central or equal to G.
2. Z(G) ⊆ F_q^× I_2.
3. G/Z(G) is an infinite, finitely generated, simple group with property (T), and it is LEF, hence sofic and
   hyperlinear.

Together with `subshift-elementary-group-is-simple-modulo-centre`, the note's theorem holds modulo the centre for
every finite field and every rank n ≥ 2.

**Mechanism.**
- A noncentral g fails to commute with a root e_ij(e_V) or e_ij(e_V u) over a small clopen V. Scalars λI_2 are the
  only elements commuting with all of them.
- k = [g,h] lies in a copy of GL_d(F_q), d = 2(2w+3), over the height-(w+1) tower on V. Its difference from I_2 never
  touches the top tower level, so k is not scalar.
- The copy of SL_d(F_q) is quasisimple and normalized by k, so it lies in the normal subgroup. So e_12(e_V) ∈ N.
- The level propagates through the Peirce blocks e_VE_11, e_VE_22 and (1−e_V)I_2 of M_2(R), which are full by
  minimality, so N = G.

**Scope.** Property (T) and finite generation rest on `complementary-full-idempotents-make-el-2-kazhdan`, which is
unreviewed. The simplicity statement (items 1–2) uses no (T).
