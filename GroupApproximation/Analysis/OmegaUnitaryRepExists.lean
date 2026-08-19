import GroupApproximation.Analysis.VectorOmegaAction
import GroupApproximation.Sofic.OpAlmostRepresentation

/-!
# Something produces an `OmegaUnitaryRep`

`VectorOmegaAction.OmegaUnitaryRep Y ω G` is the manuscript's family
`V_{g,n}` of coordinate unitaries whose multiplication defect vanishes along
`ω`, and the whole normal-Kazhdan chain --- `manuscriptNormalKazhdanSpectralGap`,
`manuscriptNormalKazhdanFixedSpace`, `manuscriptNormalKazhdanConjugation`,
their corona forms, and the corner assembly --- takes one as a hypothesis.

Until now **nothing in the development constructed one.**  A theorem whose
premise is a structure the corpus never produces is available only to a caller
who supplies it, and the standing order on this manuscript is that such a
theorem does not count as formalizing anything: the chain could have been
vacuous and no gate would have said so.  `scripts/check_ledger_unconditional.py`
is the gate that now says so, and this module is the answer to what it found.

## What is proved

* `OmegaUnitaryRep.const` --- the constant family.  Every group, every model
  sequence and every ultrafilter has one, so the structure is inhabited and
  the chain is not vacuous.  This is the weak statement.

* `OmegaUnitaryRep.ofOpAlmostRepresentation` --- **the one that matters**: an
  ordinary operator-norm asymptotic representation of `G`, which is what the
  manuscript's Section 2 constructs and what an MF embedding delivers, *is* an
  `ω`-unitary family for every ultrafilter refining the cofinite filter.  The
  reason is that ordinary convergence implies convergence along any such
  ultrafilter, which is `IsNullMatrixSequence.mono`.

  So the normal-Kazhdan chain applies to the objects the manuscript actually
  has, and its hypothesis is not an extra assumption but a weakening of the
  printed one.

## Manuscript status

Discharges the `OmegaUnitaryRep` premise of the `NK.*` rows; certifies no
manuscript step on its own.
-/

namespace GroupApproximation
namespace VectorOmegaAction

open Filter Matrix Topology
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

/-! ## The structure is inhabited -/

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)

/-- **The constant family.**  Taking every `V_{g,n}` to be the identity matrix
gives an `ω`-unitary family with zero multiplication defect, for every group,
every model sequence and every ultrafilter.  Nothing is claimed about it
beyond existence: it is here so that `OmegaUnitaryRep` is known to be
inhabited, and so that a theorem taking one as a hypothesis is known not to be
vacuous. -/
def OmegaUnitaryRep.const (G : Type*) [Group G] : OmegaUnitaryRep Y ω G where
  V := fun n _ ↦ (1 : Matrix.unitaryGroup (Y n) ℂ)
  mul_null := by
    intro g h
    have hzero :
        unitarySeq Y (fun n _ ↦ (1 : Matrix.unitaryGroup (Y n) ℂ)) (g * h)
          - unitarySeq Y (fun n _ ↦ (1 : Matrix.unitaryGroup (Y n) ℂ)) g
            * unitarySeq Y (fun n _ ↦ (1 : Matrix.unitaryGroup (Y n) ℂ)) h
          = 0 := by
      ext n
      simp
    rw [hzero]
    exact IsNullMatrixSequence.zero (Idx Y) (ω : Filter ℕ)

/-! ## An ordinary asymptotic representation is one -/

variable {G : Type*} [Group G]

/-- **The producer.**  An operator-norm asymptotic representation of `G` is an
`ω`-unitary family, for every ultrafilter refining the cofinite filter.

The coordinate unitaries are the same maps; only the sense in which the
multiplication defect vanishes changes, from ordinary convergence to
convergence along `ω`, and the first implies the second. -/
def OmegaUnitaryRep.ofOpAlmostRepresentation (A : OpAlmostRepresentation G)
    [∀ n, Nonempty (A.model n)] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    OmegaUnitaryRep A.model ω G where
  V := A.map
  mul_null := by
    intro g h
    have hatTop : IsNullMatrixSequence (Idx A.model) atTop
        (unitarySeq A.model A.map (g * h)
          - unitarySeq A.model A.map g * unitarySeq A.model A.map h) := by
      rw [IsNullMatrixSequence, Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (by positivity)
      refine ⟨N, fun n hn ↦ ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      have hcoord :
          ((unitarySeq A.model A.map (g * h)
              - unitarySeq A.model A.map g * unitarySeq A.model A.map h :
            BoundedMatrixSequence (Idx A.model)) : ∀ n, Matrix _ _ ℂ) n
            = (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ)
              - (A.map n g : Matrix (A.model n) (A.model n) ℂ)
                * (A.map n h : Matrix (A.model n) (A.model n) ℂ) := by
        simp
      calc ‖((unitarySeq A.model A.map (g * h)
                - unitarySeq A.model A.map g * unitarySeq A.model A.map h :
              BoundedMatrixSequence (Idx A.model)) : ∀ n, Matrix _ _ ℂ) n‖
          = ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ)
              - (A.map n g : Matrix (A.model n) (A.model n) ℂ)
                * (A.map n h : Matrix (A.model n) (A.model n) ℂ)‖ := by
            rw [hcoord]
        _ ≤ ε / 2 := hN n hn
        _ < ε := by linarith
    exact IsNullMatrixSequence.mono (Idx A.model) atTop
      (le_trans hω (le_of_eq Nat.cofinite_eq_atTop)) hatTop

/-- The same statement without an instance argument: an asymptotic
representation's models are nonempty by its own field, so the family exists
outright. -/
theorem nonempty_omegaUnitaryRep_of_opAlmostRepresentation
    (A : OpAlmostRepresentation G) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    letI : ∀ n, Nonempty (A.model n) := fun n ↦
      Fintype.card_pos_iff.mp (A.modelNonempty n)
    Nonempty (OmegaUnitaryRep A.model ω G) := by
  letI : ∀ n, Nonempty (A.model n) := fun n ↦
    Fintype.card_pos_iff.mp (A.modelNonempty n)
  exact ⟨OmegaUnitaryRep.ofOpAlmostRepresentation A ω hω⟩

end

end VectorOmegaAction
end GroupApproximation
