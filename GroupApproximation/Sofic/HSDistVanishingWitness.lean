import GroupApproximation.Sofic.FiniteNormalAverageCorner
import GroupApproximation.Sofic.NormTraceGap

/-!
# Something produces an `HSDistVanishing`

`FiniteNormalAverageCorner.HSDistVanishing B g h` says that the microstates of
`g` and `h` eventually coincide in normalized Hilbert--Schmidt distance, and
`false_of_finite_sum_vanishing_of_hsTrivial` --- the finite-average
contradiction the `FN.*` rows of the proof ledger grade --- takes one for every
element of the finite subgroup.

No declaration in the corpus **concluded** an `HSDistVanishing`.  The witnesses
existed, but only as `have` steps inside the proofs of
`ManuscriptCentralSignCriterion` and `FiniteNormalCompressionObstruction`, so a
gate reading conclusions saw a predicate nothing produces --- the shape of a
premise that could be unsatisfiable, making the theorem that consumes it
vacuous.  `scripts/check_ledger_unconditional.py` reports exactly that, and
this module answers it with named producers.

## What is proved

* `hsDistVanishing_rfl` --- the predicate is reflexive.  The cheap witness,
  and enough to show the premise is satisfiable.
* `hsDistVanishing_of_forall_eq` --- microstates that agree at every stage.
* `hsDistVanishing_of_opNormVanishing` --- **the one with content**: operator-norm
  closeness implies Hilbert--Schmidt closeness, because `‖x‖₂ ≤ ‖x‖`
  (`NormTraceGap.hsDistSq_le_sq_l2_opNorm`).  This is the printed inequality of
  the preliminaries, read in the vocabulary the finite-average argument uses,
  and it is how the sign criterion's own witness is really obtained.

## Manuscript status

Discharges the `HSDistVanishing` premise of the `FN.*` rows; certifies no
manuscript step on its own.
-/

namespace GroupApproximation
namespace FiniteNormalAverageCorner

open Matrix
open scoped Matrix.Norms.L2Operator

variable {E : Type} [Group E]

section Witnesses

variable (B : OpAlmostRepresentation E)

/-- **The predicate is reflexive**: a microstate is at Hilbert--Schmidt
distance zero from itself. -/
theorem hsDistVanishing_rfl (g : E) : HSDistVanishing B g g := by
  intro epsilon hepsilon
  refine ⟨0, fun n _ ↦ ?_⟩
  rw [hsDistSq_self]
  exact hepsilon.le

/-- Microstates that agree at every stage are Hilbert--Schmidt close. -/
theorem hsDistVanishing_of_forall_eq {g h : E}
    (hgh : ∀ n, (B.map n g : Matrix (B.model n) (B.model n) ℂ) = B.map n h) :
    HSDistVanishing B g h := by
  intro epsilon hepsilon
  refine ⟨0, fun n _ ↦ ?_⟩
  rw [hgh n, hsDistSq_self]
  exact hepsilon.le

/-- **Operator-norm closeness implies Hilbert--Schmidt closeness.**

This is the printed inequality `‖x‖₂ ≤ ‖x‖` of the preliminaries, read in the
vocabulary of the finite-average argument: a defect that vanishes in operator
norm vanishes in normalized Hilbert--Schmidt norm, and the converse is exactly
what `sec:limits` shows to fail.  It is the honest producer of the premise,
since it is how the sign criterion obtains its own witness. -/
theorem hsDistVanishing_of_opNormVanishing {g h : E}
    (hvan : KazhdanCornerMatrices.OpNormVanishing B
      (fun n ↦ (B.map n g : Matrix (B.model n) (B.model n) ℂ) - B.map n h)) :
    HSDistVanishing B g h := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hvan (Real.sqrt epsilon) (Real.sqrt_pos.mpr hepsilon)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hle := hN n hn
  have hsq : ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ) - B.map n h‖ ^ 2
      ≤ Real.sqrt epsilon ^ 2 :=
    by nlinarith [norm_nonneg ((B.map n g : Matrix (B.model n) (B.model n) ℂ)
      - B.map n h), Real.sqrt_nonneg epsilon]
  have hroot : Real.sqrt epsilon ^ 2 = epsilon :=
    Real.sq_sqrt hepsilon.le
  calc hsDistSq (B.model n) (B.map n g) (B.map n h)
      ≤ ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ) - B.map n h‖ ^ 2 :=
        hsDistSq_le_sq_l2_opNorm (B.model n) _ _
    _ ≤ Real.sqrt epsilon ^ 2 := hsq
    _ = epsilon := hroot

end Witnesses

end FiniteNormalAverageCorner
end GroupApproximation
