/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Countable.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.Order.Field

/-!
# A non-MF group

The theorem states that a countable group fails the sequential operator-norm
form of the Carrión--Dadarlat--Eckhardt MF property.
-/

namespace NonMFExistence

open scoped Matrix.Norms.L2Operator

noncomputable section

-- BEGIN SHARED BLOCK (kept byte-identical with `PalomarSolution.lean`)

/-- A finite index type for matrix models. -/
structure FiniteCarrier where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteCarrierCoeSort : CoeSort FiniteCarrier Type :=
  ⟨FiniteCarrier.carrier⟩

@[reducible, instance] def finiteCarrierFintype (Y : FiniteCarrier) :
    Fintype Y :=
  Y.fintype

@[reducible, instance] def finiteCarrierDecidableEq (Y : FiniteCarrier) :
    DecidableEq Y :=
  Y.decidableEq

/-- The sequential operator-norm form of the MF property for countable groups. -/
def IsSequentialOperatorMFGroup (G : Type) [Group G] : Prop :=
  ∃ (Y : ℕ → FiniteCarrier) (U : ∀ n, G → Matrix (Y n) (Y n) ℂ),
    (∀ n, 0 < Fintype.card (Y n)) ∧
    (∀ n g, U n g ∈ Matrix.unitaryGroup (Y n) ℂ) ∧
    (∀ g h : G, Filter.Tendsto
      (fun n ↦ ‖U n (g * h) - U n g * U n h‖) Filter.atTop (nhds 0)) ∧
    (∀ g : G, g ≠ 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in Filter.atTop, δ ≤ ‖U n g - 1‖)

-- END SHARED BLOCK

/-- There exists a countable group that is not MF. -/
theorem exists_countable_not_MF :
    ∃ (G : Type) (_ : Group G), Countable G ∧
      ¬ IsSequentialOperatorMFGroup G := by
  sorry

end

end NonMFExistence
