/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Countable.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.Order.Field
import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Sofic.MarkedCompressionSequentialKill
import GroupApproximation.Sofic.NormMFConsequences
import GroupApproximation.Meta.AxiomGuard

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

open GroupApproximation

/-- The marked-compression data for the countable witness group. -/
noncomputable def witnessData :
    MarkedCompressionInclusionData ExplicitNonMFBase.Base
      MarkedCompression.Explicit.theGroup where
  iota := MarkedCompression.Explicit.theIota
  t := MarkedCompression.Explicit.theT
  c := MarkedCompression.Explicit.theC
  a := ExplicitNonMFBase.omitted
  kazhdan := ExplicitNonMFBase.base_hasKazhdanPropertyT
  compresses g := ⟨ExplicitNonMFBase.compression g,
    MarkedCompression.Explicit.theCompress g⟩
  comm_c := MarkedCompression.Explicit.theCommC
  word_sq := MarkedCompression.Explicit.theWordSq
  word_central := MarkedCompression.Explicit.theWordCentral

/-- There exists a countable group that is not MF. -/
theorem exists_countable_not_MF :
    ∃ (G : Type) (_ : Group G), Countable G ∧
      ¬ IsSequentialOperatorMFGroup G := by
  let G := MarkedCompression.Explicit.theGroup
  refine ⟨G, inferInstance, inferInstance, ?_⟩
  rintro ⟨Y, U, _, hU, hmul, hsep⟩
  let w : G := witnessData.word
  have hzero : Filter.Tendsto (fun n ↦ ‖U n w - 1‖)
      Filter.atTop (nhds 0) := by
    have main : ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in Filter.atTop, ‖U n w - 1‖ < ε := by
      intro ε hε
      obtain ⟨δ, F, hδ, hbound⟩ :=
        uniform_invisibility witnessData.word_normMFInvisible ε hε
      have key : ∀ᶠ n in Filter.atTop, ∀ g ∈ F, ∀ h ∈ F,
          ‖U n (g * h) - U n g * U n h‖ ≤ δ := by
        rw [Filter.eventually_all_finset]
        intro g _
        rw [Filter.eventually_all_finset]
        intro h _
        exact (hmul g h).eventually_le_const hδ
      filter_upwards [key] with n hn
      exact hbound ⟨(Y n).carrier, (Y n).fintype, (Y n).decidableEq⟩
        (fun g ↦ ⟨U n g, hU n g⟩) hn
    refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (main ε hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact hN n hn
  obtain ⟨δ, hδ, hgap⟩ := hsep w MarkedCompression.Explicit.theWordNeOne
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hzero δ hδ
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hgap
  let n := max N M
  have hnear := hN n (le_max_left N M)
  have hfar := hM n (le_max_right N M)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hnear
  exact (not_lt_of_ge hfar) hnear

#audit_axioms NonMFExistence.exists_countable_not_MF

end

end NonMFExistence
