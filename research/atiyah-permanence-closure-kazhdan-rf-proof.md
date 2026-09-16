---
rg: 2
id: atiyah-permanence-closure-kazhdan-rf-proof
kind: route
title: Fix a vertex, finite images and diagonal embeddings keep Kazhdan subgroups residually finite; Deligne's level-3 lattice escapes
target: atiyah-permanence-closure-kazhdan-subgroups-are-rf
requires:
  - property-t-implies-property-fa
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - two-generator-fp-torsion-free-universal-whitehead-container
artifacts:
  - research/artifacts/atiyah-permanence-closure-kazhdan-rf-2026-09-16.md
---

Full proof: artifact Sections 1--4.  Standard facts used without proof:
- property (T) passes to quotients and to finite-index subgroups, and a (T)
  group is finitely generated (Bekka--de la Harpe--Valette);
- Bass--Serre theory (Serre, *Trees*, Chapter I);
- Reidemeister--Schreier, and P. Hall's lemma on extensions of finitely
  presented groups.

Let `L` be a finitely generated (T) subgroup of `G`.

**Item 1.**
- *Base.*  Subgroups of residually finite groups are residually finite.  In a
  T-finite group `L` is finite.
- *(C1), (C2).*  `L` lies in the subgroup, or in one member of the directed
  family.
- *(C3).*  `L` has FA by `property-t-implies-property-fa`.  The Bass--Serre
  action has no inversions, so `L` fixes a vertex and `g^-1 L g <= G_v`.
  This conjugate is residually finite, hence so is `L`.
- *(C4).*  The image of `L` in the T-finite group `G/N` has (T), so it is
  finite.  Then `L cap N` has finite index in `L`, is finitely generated with
  (T), and is residually finite.  A group with a residually finite subgroup of
  finite index is residually finite (take normal cores).
- *(C6).*  Each image `pi_i(L)` is residually finite, and the diagonal map
  `L -> prod pi_i(L)` is injective.  (C5) is the case of two factors.

**Item 2.**  By `deligne-universal-cover-lattice-is-non-rf-kazhdan`,
`Gamma~ = p^-1(Sp_2n(Z))` is Kazhdan and not residually finite, `ker p = Z`
is central, and `Sp_2n(Z)` is finitely presented.
- `Lambda` has finite index in `Gamma~`, so it has (T).  It is not residually
  finite, since otherwise `Gamma~` would be.
- `Gamma'` is finitely presented by Reidemeister--Schreier, so `Lambda`, an
  extension of `Z` by `Gamma'`, is finitely presented.
- The kernel of `GL_m(Z) -> GL_m(Z/3Z)` is torsion-free.  The proof takes
  `g = I + 3^a Y` of prime order `l` with `Y` not divisible by 3 and expands
  `g^l = I` modulo powers of 3 (artifact Section 3).  So `Gamma'` is
  torsion-free.
- A finite-order element of `Lambda` maps to 1, so it lies in `ker p = Z`
  and is trivial.

**Item 3.**  A group in `T` containing `Lambda` would put `Lambda` in `T` by
(C1).  `Lambda` is finitely presented and torsion-free, so
`two-generator-fp-torsion-free-universal-whitehead-container` embeds it in
`E`.  This is the embedding property that
`master-host-satisfies-algebraic-strong-atiyah` states for its host `E`.  `∎`
