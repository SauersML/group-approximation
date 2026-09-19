/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Palomar.BooneHigmanSolution

/-!
# Model tests for the Boone–Higman megasubmission shared block

Definitions of the shared block of `Palomar/BooneHigmanChallenge.lean` are tested on positive
and negative models, so that a vacuous or always-true definition cannot pass. The copies tested
here are the solution's, which are byte-identical to the challenge's.

* `IsClassTransposition`: the identity is not a class transposition.
* `IsResidueClassWiseAffine`: the identity is residue-class-wise affine.
* `IsClassShift` and `IsClassReflection`: `n ↦ n + 1` is a class shift and `n ↦ -n` a class
  reflection; the identity is neither.

Not yet tested here: that `LeavittResolventRing` is nonzero (it has a faithful module on
finitely supported functions of infinite words; see the development) and that the Steinberg
relations do not collapse `SteinbergGroup`.

The prose of this module was written by Claude (Anthropic), under the user's direction.
-/

namespace BooneHigman.ModelTests

open Equiv

/-- **Negative model.** The identity is not a class transposition: it would have to move
`r₁` to `r₂`, which lies in a disjoint class. -/
theorem one_not_isClassTransposition : ¬ IsClassTransposition 1 := by
  rintro ⟨r₁, m₁, r₂, m₂, -, -, -, -, hdisj, hswap, -⟩
  have h := (hswap 0).1
  apply hdisj 0 0
  simpa using h

/-- **Positive model.** The identity is residue-class-wise affine. -/
theorem one_isResidueClassWiseAffine : IsResidueClassWiseAffine 1 :=
  ⟨1, one_pos, fun _ => ⟨1, 0, 1, one_ne_zero, fun _ => by simp⟩⟩

/-- **Positive model.** `n ↦ n + 1` is the class shift `ν_{0(1)}`. -/
theorem addRight_one_isClassShift : IsClassShift (Equiv.addRight (1 : ℤ)) :=
  ⟨0, 1, le_refl 0, one_pos, fun t => by simp, fun n hn => (hn n (by omega)).elim⟩

/-- **Negative model.** The identity is not a class shift. -/
theorem one_not_isClassShift : ¬ IsClassShift 1 := by
  rintro ⟨r, m, h0, hm, hshift, -⟩
  have h := hshift 0
  simp at h
  omega

/-- **Positive model.** `n ↦ -n` is the class reflection `ς_{0(1)}`. -/
theorem neg_isClassReflection : IsClassReflection (Equiv.neg ℤ) :=
  ⟨0, 1, le_refl 0, one_pos, fun t => by simp, fun n hn => (hn n (by omega)).elim⟩

/-- **Negative model.** The identity is not a class reflection. -/
theorem one_not_isClassReflection : ¬ IsClassReflection 1 := by
  rintro ⟨r, m, h0, hm, hrefl, -⟩
  have h := hrefl 1
  simp at h
  omega

end BooneHigman.ModelTests
