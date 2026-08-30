---
rg: 2
id: stw99-problem-xlvii-af-cartan-criterion
kind: claim
title: Cantor C*-diagonals in AF algebras are AF Cartans (STW Problem XLVII, sharp form)
root: true
artifacts:
  - research/artifacts/stw99-presentations-cartan-cluster-2026-08-30.md
---

**Problem XLVII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
asks (in Effros's deliberately vague style) for an abstract criterion
recognising AF Cartans among Cantor-spectrum Cartans in AF algebras.
Encoded here in the sharp testable form the literature pins down: is
every C\*-DIAGONAL (Cartan with the unique extension property) with
Cantor spectrum in an AF algebra an AF Cartan?

Known: AF Cartans are unique up to automorphism (Power), and are
C\*-diagonals with Cantor spectrum; Mitscher--Spielberg construct
non-AF Cantor CARTANS in irrational-rotation AF algebras, but their
examples come from non-principal groupoids, hence fail the unique
extension property — STW record that no non-AF Cantor DIAGONAL in an
AF algebra is known.  So principality (= diagonality) is the candidate
criterion, unrefuted.

## Attempts

* Positive strategy: a Cantor diagonal gives a principal étale
  groupoid model of the AF algebra; AF-ness of the algebra plus
  principality should force the groupoid to be an AF equivalence
  relation — this is a groupoid-homology/dimension statement
  (principal + `dim_nuc = 0` ⟹ AF groupoid?) that fails for
  non-principal groupoids (Mitscher--Spielberg have nuclear dimension
  0 models with nontrivial isotropy) and is open for principal ones;
  the missing tool is exactness of the passage from local finiteness
  of the ALGEBRA to local finiteness of the RELATION, a Feldman--Moore
  style statement outside the measured setting.  Refutation strategy:
  run Mitscher--Spielberg with an isotropy-free replacement groupoid —
  their K-theory bookkeeping does not obviously need the isotropy, so
  this problem is live in both directions and is flagged as the
  cheapest place in this cluster where a counterexample might drop.
