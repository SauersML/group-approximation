import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Polar.ExtendClosedGraph
import Mathlib.Topology.Algebra.Star
import GroupApproximation.Meta.AxiomGuard

/-!
# Absolute value, lane `nm-tww-17a`: the carrier as a normed space

This file gives the carrier of a Hilbert module `E` a normed space structure, as scoped
instances in `KasparovStab.AbsOp`. The norm is `E.norm` by definition. Contents:
* `norm_eq`: `‖x‖ = E.norm x`.
* `completeSpace_of_isCompleteModule`: `IsCompleteModule E` gives `CompleteSpace E.carrier`.
  The proof is the one in `ExtendClosedGraph`.
* `tendsto_inner_right_of_tendsto` and `tendsto_inner_left_of_tendsto`: the inner product is
  continuous in each slot. The left slot follows from the right one by `inner_star`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp

open GroupApproximation.HilbertModule Filter Topology

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The carrier of a Hilbert module, as a normed group. -/
noncomputable scoped instance instNormedAddCommGroup (E : CStarModule.{v, v} B) :
    NormedAddCommGroup E.carrier :=
  E.toNormedAddCommGroup

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.instNormedAddCommGroup

/-- The carrier of a Hilbert module, as a normed space. -/
noncomputable scoped instance instNormedSpace (E : CStarModule.{v, v} B) :
    NormedSpace ℂ E.carrier :=
  { norm_smul_le := fun c x => le_of_eq (E.norm_smul c x) }

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.instNormedSpace

theorem norm_eq {E : CStarModule.{v, v} B} (x : E.carrier) : ‖x‖ = E.norm x := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.norm_eq

/-- Metric convergence is `IsLimit`. -/
theorem isLimit_of_tendsto {E : CStarModule.{v, v} B} {u : ℕ → E.carrier} {a : E.carrier}
    (hu : Tendsto u atTop (𝓝 a)) : IsLimit E u a := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu ε hε
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [dist_eq_norm_sub, norm_eq] at h
  exact h.le

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.isLimit_of_tendsto

/-- A complete module has a complete carrier. -/
theorem completeSpace_of_isCompleteModule {E : CStarModule.{v, v} B}
    (hE : IsCompleteModule E) : CompleteSpace E.carrier := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hc : IsCauchy E u := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm_sub, norm_eq] at h
    exact h.le
  obtain ⟨y, hy⟩ := hE u hc
  refine ⟨y, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hy (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm_sub, norm_eq]
  exact lt_of_le_of_lt (hN n hn) (half_lt_self hε)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.completeSpace_of_isCompleteModule

/-- The inner product is continuous in its second slot. -/
theorem tendsto_inner_right_of_tendsto {E : CStarModule.{v, v} B} {u : ℕ → E.carrier}
    {a : E.carrier} (hu : Tendsto u atTop (𝓝 a)) (x : E.carrier) :
    Tendsto (fun n => E.inner x (u n)) atTop (𝓝 (E.inner x a)) :=
  (isLimit_of_tendsto hu).tendsto_inner_right x

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.tendsto_inner_right_of_tendsto

/-- The inner product is continuous in its first slot. -/
theorem tendsto_inner_left_of_tendsto {E : CStarModule.{v, v} B} {u : ℕ → E.carrier}
    {a : E.carrier} (hu : Tendsto u atTop (𝓝 a)) (y : E.carrier) :
    Tendsto (fun n => E.inner (u n) y) atTop (𝓝 (E.inner a y)) := by
  have h := (tendsto_inner_right_of_tendsto hu y).star
  simpa only [E.inner_star] using h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp.tendsto_inner_left_of_tendsto

end GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AbsOp
