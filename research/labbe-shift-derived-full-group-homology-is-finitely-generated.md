---
rg: 2
id: labbe-shift-derived-full-group-homology-is-finitely-generated
kind: claim
title: Labbé's derived full group has H_2 = Z plus a finite 2-group and finitely generated homology in every degree, so homology and additive relation invariants cannot refute its finite presentation
invalidates:
  - labbe-not-fp-via-infinitely-generated-homology
  - labbe-not-fp-via-mean-area-relation-invariant
distinct_from:
  labbe-shift-derived-full-group-is-finitely-presented: That is the open finite presentation question; this proves that the homological and additive-invariant obstructions to it vanish, which neither establishes nor refutes it.
  penrose-derived-full-group-homology-is-finitely-generated: That is the same conclusion for the Penrose group, from Li's computation of the Penrose groupoid homology; this derives it for Labbé's Wang shift from recognizable self-similarity.
  labbe-shift-derived-full-group-escapes-known-obstructions: That shows the recorded dynamical obstructions do not fire; this shows every homological and additive relation-invariant obstruction does not fire either.
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-labbe-2026-09-13.md
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Gamma = D([[Z^2 ~ Omega_U]])` for Labbé's 19-tile Wang shift.

1. **Degree 2.** `H_2(Gamma; Z) ≅ Z ⊕ T`, where `T` is a finite abelian 2-group of exponent at most 4.
2. **All degrees.** `H_j(Gamma; Z)` is finitely generated for every `j`.
3. **Relation invariants.** Let `F` be free on a finite generating set and `N` the relation
   subgroup. Every conjugation-invariant homomorphism `N -> A` has finitely generated image.
   - Examples are the mean signed area of relator loops against the invariant measure, and any
     other invariant-measure "relation compression" invariant of additive type.

**Consequence.** Neither route can refute
`labbe-shift-derived-full-group-is-finitely-presented`:
- showing some `H_j(Gamma)` is infinitely generated;
- exhibiting an additive relation invariant with infinitely generated values.

This upgrades the heuristic remark "Homology gives no obstruction" in that claim's Attempts, which
concerned only Li's low-degree exact sequence, to a theorem in every degree.
- **What remains.** A refutation must be nonabelian. The recorded candidate is
  `labbe-shift-derived-full-group-is-lef`.

Proof: `labbe-derived-full-group-homology-proof`.
