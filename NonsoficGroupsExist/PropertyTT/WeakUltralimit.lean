import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Separation.Hausdorff

/-!
# Weak ultralimits of bounded Hilbert-space sequences

This file packages the Banach--Alaoglu construction needed for invariant
averaging.  It uses the canonical nonprincipal ultrafilter on `ℕ`, takes the
ultralimit in a weak-star compact dual ball, and returns to the Hilbert space
by the Fréchet--Riesz equivalence.
-/

namespace NonsoficGroupsExist

open Filter Metric
open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The weak-star closed dual ball used as a compact target. -/
def weakDualClosedBall (E : Type v) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (C : ℝ) :=
  {phi : WeakDual ℂ E //
    WeakDual.toStrongDual phi ∈ closedBall (0 : StrongDual ℂ E) C}

noncomputable instance weakDualClosedBall.topologicalSpace (C : ℝ) :
    TopologicalSpace (weakDualClosedBall E C) :=
  TopologicalSpace.induced Subtype.val inferInstance

noncomputable instance weakDualClosedBall.compactSpace (C : ℝ) :
    CompactSpace (weakDualClosedBall E C) :=
  isCompact_iff_compactSpace.mp
    (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) C)

/-- A bounded vector, regarded as a point of the weak-star compact dual
ball through Fréchet--Riesz. -/
noncomputable def toWeakDualClosedBall (x : ℕ → E) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (n : ℕ) : weakDualClosedBall E C :=
  ⟨(InnerProductSpace.toDual ℂ E (x n)).toWeakDual, by
    change dist (InnerProductSpace.toDual ℂ E (x n)) 0 ≤ C
    simpa [dist_eq_norm] using hx n⟩

/-- Weak ultralimit of a norm-bounded Hilbert-space sequence. -/
noncomputable def weakUltralimit (x : ℕ → E) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) : E :=
  (InnerProductSpace.toDual ℂ E).symm
    (WeakDual.toStrongDual
      (Ultrafilter.map (toWeakDualClosedBall x C hx)
        (hyperfilter ℕ)).lim.1)

/-- The weak ultralimit remains in the same norm ball. -/
theorem norm_weakUltralimit_le (x : ℕ → E) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) :
    ‖weakUltralimit x C hx‖ ≤ C := by
  let U : Ultrafilter (weakDualClosedBall E C) :=
    Ultrafilter.map (toWeakDualClosedBall x C hx) (hyperfilter ℕ)
  have hmem := U.lim.property
  change dist (WeakDual.toStrongDual U.lim.1) 0 ≤ C at hmem
  change ‖(InnerProductSpace.toDual ℂ E).symm
    (WeakDual.toStrongDual U.lim.1)‖ ≤ C
  rw [(InnerProductSpace.toDual ℂ E).symm.norm_map]
  simpa [dist_eq_norm] using hmem

/-- Evaluation against every test vector converges to evaluation against
the weak ultralimit. -/
theorem tendsto_inner_weakUltralimit (x : ℕ → E) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (y : E) :
    Tendsto (fun n ↦ ⟪x n, y⟫_ℂ) (hyperfilter ℕ)
      (nhds ⟪weakUltralimit x C hx, y⟫_ℂ) := by
  let f : ℕ → weakDualClosedBall E C := toWeakDualClosedBall x C hx
  let U : Ultrafilter (weakDualClosedBall E C) :=
    Ultrafilter.map f (hyperfilter ℕ)
  have hlim : (U : Filter (weakDualClosedBall E C)) ≤ nhds U.lim :=
    U.le_nhds_lim
  have heval : Continuous (fun phi : weakDualClosedBall E C ↦
      (WeakDual.toStrongDual phi.1) y) := by
    exact (WeakDual.eval_continuous y).comp continuous_subtype_val
  have ht := (heval.tendsto U.lim).comp hlim
  change Tendsto (fun n ↦
      (WeakDual.toStrongDual (f n).1) y) (hyperfilter ℕ)
      (nhds ((WeakDual.toStrongDual
        U.lim.1) y)) at ht
  simpa [f, U, toWeakDualClosedBall, weakUltralimit] using ht

/-- The weak ultralimit is independent of the numerical bound used to
place the sequence in a compact dual ball. -/
theorem weakUltralimit_congr_bound (x : ℕ → E) (C K : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (hk : ∀ n, ‖x n‖ ≤ K) :
    weakUltralimit x C hx = weakUltralimit x K hk := by
  apply ext_inner_right ℂ
  intro y
  exact tendsto_nhds_unique
    (tendsto_inner_weakUltralimit x C hx y)
    (tendsto_inner_weakUltralimit x K hk y)

/-- Eventually equal bounded sequences have the same weak ultralimit. -/
theorem weakUltralimit_eq_of_eventuallyEq (x z : ℕ → E) (C K : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (hz : ∀ n, ‖z n‖ ≤ K)
    (hxz : x =ᶠ[hyperfilter ℕ] z) :
    weakUltralimit x C hx = weakUltralimit z K hz := by
  apply ext_inner_right ℂ
  intro y
  exact tendsto_nhds_unique
    ((tendsto_inner_weakUltralimit x C hx y).congr'
      (hxz.fun_comp fun w ↦ ⟪w, y⟫_ℂ).symm)
    (tendsto_inner_weakUltralimit z K hz y)

/-- A unitary operator commutes with weak ultralimits. -/
theorem weakUltralimit_linearIsometryEquiv
    (U : E ≃ₗᵢ[ℂ] E) (x : ℕ → E) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C)
    (hUx : ∀ n, ‖U (x n)‖ ≤ C) :
    weakUltralimit (fun n ↦ U (x n)) C hUx =
      U (weakUltralimit x C hx) := by
  apply ext_inner_right ℂ
  intro y
  apply tendsto_nhds_unique
    (tendsto_inner_weakUltralimit (fun n ↦ U (x n)) C hUx y)
  simpa only [U.inner_map_eq_flip] using
    tendsto_inner_weakUltralimit x C hx (U.symm y)

/-- Weak ultralimits commute with addition.  The bounds and their proofs are
allowed to differ: only the represented bounded sequences matter. -/
theorem weakUltralimit_add (x z : ℕ → E) (C K : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (hz : ∀ n, ‖z n‖ ≤ K)
    (hxz : ∀ n, ‖x n + z n‖ ≤ C + K) :
    weakUltralimit (fun n ↦ x n + z n) (C + K) hxz =
      weakUltralimit x C hx + weakUltralimit z K hz := by
  apply ext_inner_right ℂ
  intro y
  apply tendsto_nhds_unique
    (tendsto_inner_weakUltralimit (fun n ↦ x n + z n) (C + K) hxz y)
  simpa only [inner_add_left] using
    (tendsto_inner_weakUltralimit x C hx y).add
      (tendsto_inner_weakUltralimit z K hz y)

/-- Weak ultralimits commute with negation. -/
theorem weakUltralimit_neg (x : ℕ → E) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C)
    (hneg : ∀ n, ‖-x n‖ ≤ C) :
    weakUltralimit (fun n ↦ -x n) C hneg =
      -weakUltralimit x C hx := by
  apply ext_inner_right ℂ
  intro y
  apply tendsto_nhds_unique
    (tendsto_inner_weakUltralimit (fun n ↦ -x n) C hneg y)
  simpa only [inner_neg_left] using
    (tendsto_inner_weakUltralimit x C hx y).neg

/-- Weak ultralimits commute with subtraction. -/
theorem weakUltralimit_sub (x z : ℕ → E) (C K : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (hz : ∀ n, ‖z n‖ ≤ K)
    (hxz : ∀ n, ‖x n - z n‖ ≤ C + K) :
    weakUltralimit (fun n ↦ x n - z n) (C + K) hxz =
      weakUltralimit x C hx - weakUltralimit z K hz := by
  apply ext_inner_right ℂ
  intro y
  apply tendsto_nhds_unique
    (tendsto_inner_weakUltralimit (fun n ↦ x n - z n) (C + K) hxz y)
  simpa only [inner_sub_left] using
    (tendsto_inner_weakUltralimit x C hx y).sub
      (tendsto_inner_weakUltralimit z K hz y)

/-- A uniform pointwise distance bound survives passage to weak
ultralimits. -/
theorem norm_weakUltralimit_sub_le (x z : ℕ → E) (C K D : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) (hz : ∀ n, ‖z n‖ ≤ K)
    (hxz : ∀ n, ‖x n - z n‖ ≤ D) :
    ‖weakUltralimit x C hx - weakUltralimit z K hz‖ ≤ D := by
  have hsubBound : ∀ n, ‖x n - z n‖ ≤ C + K := by
    intro n
    exact (norm_sub_le (x n) (z n)).trans (add_le_add (hx n) (hz n))
  rw [← weakUltralimit_sub x z C K hx hz hsubBound]
  rw [weakUltralimit_congr_bound (fun n ↦ x n - z n)
    (C + K) D hsubBound hxz]
  exact norm_weakUltralimit_le (fun n ↦ x n - z n) D hxz

end NonsoficGroupsExist
