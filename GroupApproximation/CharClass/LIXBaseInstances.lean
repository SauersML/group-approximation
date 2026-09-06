import GroupApproximation.CharClass.LIXSectionManuscript

/-!
# Compactness and nonemptiness of the LIX base

Lane `cc-lix-odd`.

`cc-projective`'s Leray--Hirsch instance takes `Nonempty` and `CompactSpace` on the base,
and the mapping-torus base carried neither.  All four facts are true and none is deep;
they belong here, with the base, rather than with whichever consumer hits the gap first.

Each factor supplies its own:

* the circle is a metric sphere of radius one in a finite-dimensional real space, and this
  lane already has two points of it, `northPole` and `southPole`;
* the Hermitian five-sphere has `STW59.isCompact_unitVectors`, and `eThree` is a point;
* the projective factors have `CP.instCompactSpace` and `CP.instNonempty`, and a dependent
  product of compact nonempty spaces inherits both.

## Main results

* `sphereOne.instCompactSpace`, `sphereOne.instNonempty`.
* `unitVectorsThree.instCompactSpace`, `unitVectorsThree.instNonempty`.
* `baseM` and the full base `↥sphereOne × baseM dd` then get theirs by inference.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-! ## 1. The circle -/

instance sphereOne.instCompactSpace : CompactSpace ↥sphereOne :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

instance sphereOne.instNonempty : Nonempty ↥sphereOne := ⟨southPole⟩

/-! ## 2. The Hermitian five-sphere -/

instance unitVectorsThree.instCompactSpace : CompactSpace ↥(unitVectors (Fin 3)) :=
  isCompact_iff_compactSpace.mp (isCompact_unitVectors (Fin 3))

instance unitVectorsThree.instNonempty : Nonempty ↥(unitVectors (Fin 3)) := ⟨negEThree⟩

/-! ## 3. The base, by inference

`baseY dd` is a dependent product of complex projective spaces, each compact and nonempty,
so it inherits both; `baseM dd` is its product with the five-sphere, and the full base is
that with the circle.  The two checks below are the ones `cc-projective`'s instance
performs. -/

example {ℓ : ℕ} (dd : Fin ℓ → ℕ) : CompactSpace (↥sphereOne × baseM dd) := inferInstance

example {ℓ : ℕ} (dd : Fin ℓ → ℕ) : Nonempty (↥sphereOne × baseM dd) := inferInstance

end GroupApproximation.CharClass
