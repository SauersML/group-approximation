---
rg: 2
id: toms-gamma-counterexample-strict-comparison-proof
kind: route
title: AH plus strict comparison forces uniform Gamma
target: toms-gamma-counterexample-fails-strict-comparison
requires: [toms-ah-counterexample-to-uniform-gamma]
artifacts:
  - research/artifacts/stw99-ranks-divisibility-cluster-2026-08-30.md
---

Four cited theorems chain into a contradiction.  Suppose `B` is a
unital simple separable nuclear non-elementary stably finite AH algebra
with strict comparison but without uniform property Γ.

1. All ranks almost occur in every unital simple non-elementary AH
   algebra (Blackadar--Perera--Toms, Crelle, Thm 5.3; the stable rank
   one hypothesis is removable by completing the Cuntz semigroup — STW
   footnote 24).
2. Strict comparison plus all ranks almost occurring is pureness, and
   pureness gives `Cu(B) ≅ Cu(B ⊗ Z)` (STW arXiv:2506.10902,
   Proposition `prop:cu-regular`, (7) ⟹ (5) ⟹ (2), for simple
   separable stably finite algebras).
3. AH algebras have locally finite nuclear dimension, so Winter's
   theorem (Invent. Math. 2012) upgrades `Cu(B) ≅ Cu(B ⊗ Z)` to
   `B ≅ B ⊗ Z`.
4. `Z`-stable algebras have uniform property Γ
   (Castillejos--Evington--Tikuisis--White--Winter), contradicting the
   hypothesis.

So no such `B` has strict comparison.  The required input supplies the
existence of at least one such `B` (Toms, arXiv:2606.12188v2, Thm 5),
making the statement non-vacuous; the argument is independent of the
internal Schubert-calculus perforation analysis of Toms's paper.
