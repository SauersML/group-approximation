import GroupApproximation.Sofic.HyperlinearAmplification
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Finite matrix measurements

This module is the finite POVM kernel needed to state finite-dimensional
strategies in the self-destroying-game / HS--PCP lane.  It deliberately reuses
this repository's `FiniteModel`, matrix-order, and normalized-trace conventions
instead of introducing a second quantum-operator hierarchy.

## Provenance and license

The compact `Submeasurement` / `Measurement` / outcome-postprocessing API is
adapted from the audit surface in
[`LionSR/LDT-comparator`](https://github.com/LionSR/LDT-comparator),
`Challenge.lean`, revision `15f1d5b2797c67ceb9d278d0a4d576772b937e9a`,
which is distributed under Apache License 2.0.  That challenge records the
corresponding source declarations in
[`LionSR/MIPStarRE`](https://github.com/LionSR/MIPStarRE), revision
`892b939c541e90192a8c77917cbb106678fd43b3`.

This is a modified port: names and namespaces are different, the ambient
operator type is specialized to this project's `FiniteModel`, the redundant
stored total is retained only where it makes postprocessing compositional, and
all proofs were re-elaborated against this repository's Mathlib revision.  The
project root `LICENSE` contains the Apache 2.0 terms.
-/

open scoped BigOperators MatrixOrder ComplexOrder

namespace GroupApproximation
namespace FiniteMeasurement

/-- Square complex operators on one of the repository's finite models. -/
abbrev Op (Y : FiniteModel) := Matrix Y Y ℂ

/-- A finite family of positive effects whose stored total is at most one. -/
structure Submeasurement (Outcome : Type*) [Fintype Outcome] (Y : FiniteModel) where
  effect : Outcome → Op Y
  total : Op Y
  effect_nonneg : ∀ a, 0 ≤ effect a
  sum_effect_eq_total : ∑ a, effect a = total
  total_le_one : total ≤ 1

/-- A finite POVM: a submeasurement whose total is the identity. -/
structure Measurement (Outcome : Type*) [Fintype Outcome] (Y : FiniteModel)
    extends Submeasurement Outcome Y where
  total_eq_one : total = 1

/-- A finite projective measurement.  Positivity inherited from `Measurement`
supplies self-adjointness, so idempotence is the only extra field needed. -/
structure ProjectiveMeasurement (Outcome : Type*) [Fintype Outcome] (Y : FiniteModel)
    extends Measurement Outcome Y where
  effect_idempotent : ∀ a, effect a * effect a = effect a

namespace Submeasurement

variable {Outcome NewOutcome : Type*} [Fintype Outcome] [Fintype NewOutcome]
variable [DecidableEq NewOutcome]
variable {Y : FiniteModel}

/-- The defining sum of a submeasurement, exposed in the useful orientation. -/
theorem total_eq_sum_effect (M : Submeasurement Outcome Y) :
    M.total = ∑ a, M.effect a :=
  M.sum_effect_eq_total.symm

/-- Relabel outcomes by summing all effects in each fiber. -/
noncomputable def postprocess (M : Submeasurement Outcome Y)
    (f : Outcome → NewOutcome) : Submeasurement NewOutcome Y := by
  classical
  exact
    { effect := fun b =>
        ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a
      total := M.total
      effect_nonneg := fun _ => Finset.sum_nonneg fun a _ => M.effect_nonneg a
      sum_effect_eq_total :=
        (Finset.sum_fiberwise Finset.univ f M.effect).trans M.sum_effect_eq_total
      total_le_one := M.total_le_one }

@[simp]
theorem postprocess_effect (M : Submeasurement Outcome Y)
    (f : Outcome → NewOutcome) (b : NewOutcome) :
    (M.postprocess f).effect b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a :=
  by simp [postprocess]

@[simp]
theorem postprocess_total (M : Submeasurement Outcome Y)
    (f : Outcome → NewOutcome) :
    (M.postprocess f).total = M.total :=
  by simp [postprocess]

/-- Outcome relabeling preserves the sum of all effects. -/
theorem sum_postprocess_effect (M : Submeasurement Outcome Y)
    (f : Outcome → NewOutcome) :
    ∑ b, (M.postprocess f).effect b = ∑ a, M.effect a := by
  rw [(M.postprocess f).sum_effect_eq_total, M.sum_effect_eq_total]
  exact postprocess_total M f

end Submeasurement

namespace Measurement

variable {Outcome NewOutcome : Type*} [Fintype Outcome] [Fintype NewOutcome]
variable [DecidableEq NewOutcome]
variable {Y : FiniteModel}

/-- Build a POVM from positive effects whose sum is the identity. -/
def ofSumEqOne (effect : Outcome → Op Y) (effect_nonneg : ∀ a, 0 ≤ effect a)
    (sum_effect_eq_one : ∑ a, effect a = 1) : Measurement Outcome Y where
  effect := effect
  total := 1
  effect_nonneg := effect_nonneg
  sum_effect_eq_total := sum_effect_eq_one
  total_le_one := le_rfl
  total_eq_one := rfl

/-- Relabeling the outcomes of a POVM again gives a POVM. -/
noncomputable def postprocess (M : Measurement Outcome Y)
    (f : Outcome → NewOutcome) : Measurement NewOutcome Y where
  toSubmeasurement := M.toSubmeasurement.postprocess f
  total_eq_one := by simpa using M.total_eq_one

@[simp]
theorem postprocess_effect (M : Measurement Outcome Y)
    (f : Outcome → NewOutcome) (b : NewOutcome) :
    (M.postprocess f).effect b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a :=
  by simp [postprocess, Submeasurement.postprocess]

@[simp]
theorem postprocess_total (M : Measurement Outcome Y)
    (f : Outcome → NewOutcome) :
    (M.postprocess f).total = 1 := by
  simpa using (M.postprocess f).total_eq_one

/-- A POVM's effects sum to the identity. -/
theorem sum_effect_eq_one (M : Measurement Outcome Y) :
    ∑ a, M.effect a = 1 :=
  M.sum_effect_eq_total.trans M.total_eq_one

/-- Postprocessing preserves completeness without exposing the stored total. -/
theorem sum_postprocess_effect_eq_one (M : Measurement Outcome Y)
    (f : Outcome → NewOutcome) :
    ∑ b, (M.postprocess f).effect b = 1 :=
  (M.postprocess f).sum_effect_eq_one

end Measurement

/-- Question-indexed finite POVMs, the measurement component of a finite
nonlocal-game strategy. -/
abbrev MeasurementFamily (Question Outcome : Type*) [Fintype Outcome]
    (Y : FiniteModel) :=
  Question → Measurement Outcome Y

/-- Relabel every measurement in a question-indexed family. -/
noncomputable def MeasurementFamily.postprocess
    {Question Outcome NewOutcome : Type*}
    [Fintype Outcome] [Fintype NewOutcome]
    [DecidableEq NewOutcome] {Y : FiniteModel}
    (M : MeasurementFamily Question Outcome Y)
    (f : Outcome → NewOutcome) : MeasurementFamily Question NewOutcome Y :=
  fun q => (M q).postprocess f

@[simp]
theorem MeasurementFamily.postprocess_effect
    {Question Outcome NewOutcome : Type*}
    [Fintype Outcome] [Fintype NewOutcome]
    [DecidableEq NewOutcome] {Y : FiniteModel}
    (M : MeasurementFamily Question Outcome Y)
    (f : Outcome → NewOutcome) (q : Question) (b : NewOutcome) :
    (M.postprocess f q).effect b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), (M q).effect a :=
  by simp [MeasurementFamily.postprocess]

end FiniteMeasurement
end GroupApproximation
