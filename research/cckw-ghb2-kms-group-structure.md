---
rg: 2
id: cckw-ghb2-kms-group-structure
kind: claim
title: The KMS group GHB_2(7) is a hyperbolic Kazhdan triangle of finite groups with a vertex-injective finite quotient
distinct_from:
  caprace-kassabov-hyperbolic-kazhdan-alternating-quotients: that imports Caprace--Kassabov's alternating quotients of the KMS group G_HC(1)(p), quoting CCKW only indirectly; this imports CCKW's own structure theorems for G_HB2(7), including the CAT(0) complex, conjugacy of finite subgroups into vertex groups, and the torsion-free kernel of a vertex-injective quotient
artifacts:
  - research/artifacts/ghb7-kernel-certified-candidate-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `G = G_{HB_2}(7)` be the group

```text
<a,b,c | a^7, b^7, c^7, [a,b,a], [a,b,b], [c,b,c], [c,b,b,c], [c,b,b,b], [c,a,c], [c,a,a,c], [c,a,a,a]>
```

(`GHB 7` in `GroupApproximation/Kazhdan/KMSGroupPresentation.lean`). Then:

1. `G` is infinite, word-hyperbolic, and has property (T) (CCKW Theorem 1.3).
2. `G` is the fundamental group of a triangle of groups with trivial face group, vertex
   groups `<a,b> ≅ U_3(7)` (order `343`), `<c,b> ≅ <c,a> ≅ U_4(7)` (order `2401`), and edge
   groups `<a>, <b>, <c>` of order `7`, of half-girth type `(3,4,4)` (CCKW §7, Prop 7.2).
3. `G` acts by simplicial isometries on a CAT(−1) 2-dimensional simplicial complex `Y`
   with a triangle as strict fundamental domain and vertex stabilizers the vertex
   groups (CCKW Theorem 3.1(i),(v)).
4. Every finite subgroup of `G` is conjugate into a vertex group, and the kernel of any
   homomorphism to a finite group that is injective on the three vertex groups is
   torsion-free of finite index (CCKW Theorem 3.1(ii),(iv)).
5. The assignments `a ↦ I + E_03 + E_12`, `b ↦ I + E_10 − E_23`, `c ↦ I + E_31` extend to a
   homomorphism `ψ : G → SL_4(F_7)` (CCKW Proposition 7.15 with `k = 1`) that is injective
   on the three vertex groups.

Items 1 (property (T)) and 5, and the link girths `6, 8, 8` behind item 2, are also
compiled on main:
- `hasKazhdanPropertyT_ghb7`;
- the relator checks in `Kazhdan/GHBQuotientMatrices.lean`;
- `injective_psi_comp_u3ToAB`, `injective_psi_comp_u4ToCB`, `injective_psi_comp_u4ToCA`;
- `cckwLinkGirths`.

CITATION
cckw-ghb2-kms-group-structure-citation
