import GroupApproximation.CharClass.LemmaTwoStepCAbsEquiv
import GroupApproximation.CharClass.LIXChernSlice

/-!
# The marked sphere point, in the transported spelling

Lane `cc-lix-odd`, for `cc-wu`'s assembly of the even side.

`hslice_of_chernSliceValue_south` takes the sphere coordinate as
`unitVectorsThreeHomeoSphere.symm p5` for a point `p5` of the vendored five-sphere, while
`cc-steenrod`'s value statement is at `negEThree` directly.  Taking
`p5 := unitVectorsThreeHomeoSphere negEThree` leaves a round trip that holds by a lemma
rather than by definition, so the two spellings do not meet on the nose.

**The cure is to name the transported form, not to force the two to coincide.**  That is
the fourth time tonight the same shape has appeared: a fact true by a lemma sitting where a
consumer expects definitional equality.  `unitVectorsThreeHomeoSphere` itself was a
restatement at a different index precisely because *that* one was free; this one is not.

The homeomorphism and the marked point are both this lane's, so the naming is this lane's.

## Main results

* `unitVectorsThreeHomeoSphere_symm_apply_negEThree` — the round trip at the marked point.
* `lixSliceMap_south_marked` — the slice map itself, at the transported spelling.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **The round trip at the marked point.** -/
@[simp] theorem unitVectorsThreeHomeoSphere_symm_apply_negEThree :
    unitVectorsThreeHomeoSphere.symm (unitVectorsThreeHomeoSphere negEThree) = negEThree :=
  unitVectorsThreeHomeoSphere.symm_apply_apply negEThree

/-- **The slice map at the transported marked point** is the slice map at the marked point.

**Cite the point lemma above, not this one, wherever the slice map appears inside the type
of a later argument.**  `cc-wu` found that at their call site `chernOf` takes the restricted
rank as a proof argument mentioning the slice map, so rewriting the map there is a dependent
rewrite whose motive does not typecheck.  Substituting the *point* moves the map and the
rank proof together; rewriting the *map* moves only one of them.

The general shape, and it is the same one this lane has been collecting all night: when two
spellings meet definitionally nowhere, move the thing everything else depends on, not the
thing you are looking at.

This statement is still the right one for a consumer whose slice map is not under a
dependent argument. -/
theorem lixSliceMap_south_marked (dd : Fin ℓ → ℕ) :
    lixSliceMap dd southPole
        (unitVectorsThreeHomeoSphere.symm (unitVectorsThreeHomeoSphere negEThree))
      = lixSliceMap dd southPole negEThree :=
  congrArg (lixSliceMap dd southPole) unitVectorsThreeHomeoSphere_symm_apply_negEThree

end GroupApproximation.CharClass
