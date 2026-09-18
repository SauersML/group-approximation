import GroupApproximation.Analysis.CStarStabilization
import GroupApproximation.Analysis.CStarFiniteRank
import GroupApproximation.Analysis.CStarCompactOperators
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: vocabulary

Lane `nm-tww-16` (cartography `lanes/carto-nm-tww.md`): `H_B ⊕ E ≅ H_B` for a
countably generated Hilbert `B`-module `E`, by the Mingo--Phillips route.

This module fixes the sequential vocabulary the other modules of the lane use.

* `IsLimit E u y` and `IsCauchy E u` are stated in the module norm `E.norm`. The
  corpus has no topology on a bundled module.
* `IsCompleteModule E`: every Cauchy sequence has a limit.
* `IsApprox S y` (`y` lies in the closure of the range of `S`) and
  `HasDenseRange S`.
* Algebraic facts the corpus lacks: `act_zero_right` and `act_smul_right`.
* Continuity of the inner product in its second slot (`IsLimit.tendsto_inner_right`).

## Truth check (loud)

The corpus statement `HilbertModule.StabilizationInput` quantifies over every
countably generated module and is **false**. Completeness is missing.
`H_B ⊕ E` contains `E` isometrically, so a unitary `H_B ⊕ E → H_B` forces `E` to be
complete (`ProdComplete.isCompleteModule_of_unitary`). For `B ≠ 0`, the finitely
supported sequences `c₀₀(B)` form a countably generated module that is not complete.
The lane proves the corrected statement, which adds `IsCompleteModule E`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule Filter Topology

universe v w w'

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- `u n → y` in the module norm. -/
def IsLimit (E : CStarModule.{v, w} B) (u : ℕ → E.carrier) (y : E.carrier) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → E.norm (u n - y) ≤ ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsLimit

/-- A Cauchy sequence in the module norm. -/
def IsCauchy (E : CStarModule.{v, w} B) (u : ℕ → E.carrier) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → E.norm (u m - u n) ≤ ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsCauchy

/-- **A complete Hilbert module** (a Hilbert C⋆-module in the strict sense). -/
def IsCompleteModule (E : CStarModule.{v, w} B) : Prop :=
  ∀ u : ℕ → E.carrier, IsCauchy E u → ∃ y : E.carrier, IsLimit E u y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsCompleteModule

/-- `y` lies in the norm closure of the range of `S`. -/
def IsApprox {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
    (S : Adjointable E F) (y : F.carrier) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x : E.carrier, F.norm (S.toFun x - y) ≤ ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsApprox

/-- `S` has dense range. -/
def HasDenseRange {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B}
    (S : Adjointable E F) : Prop :=
  ∀ y : F.carrier, IsApprox S y

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.HasDenseRange

theorem modNorm_sub_comm (E : CStarModule.{v, w} B) (x y : E.carrier) :
    E.norm (x - y) = E.norm (y - x) := by
  rw [← neg_sub y x, E.norm_neg]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.modNorm_sub_comm

theorem modNorm_sub_le (E : CStarModule.{v, w} B) (x y z : E.carrier) :
    E.norm (x - z) ≤ E.norm (x - y) + E.norm (y - z) := by
  calc E.norm (x - z) = E.norm ((x - y) + (y - z)) := by rw [sub_add_sub_cancel]
    _ ≤ E.norm (x - y) + E.norm (y - z) := E.norm_add_le _ _

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.modNorm_sub_le

theorem eq_of_norm_sub_le (E : CStarModule.{v, w} B) {x y : E.carrier}
    (h : ∀ ε : ℝ, 0 < ε → E.norm (x - y) ≤ ε) : x = y := by
  have h0 : E.norm (x - y) = 0 := by
    refine le_antisymm ?_ (E.norm_nonneg _)
    by_contra hlt
    push Not at hlt
    have h1 := h (E.norm (x - y) / 2) (half_pos hlt)
    linarith
  exact sub_eq_zero.mp ((E.norm_eq_zero_iff _).mp h0)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.eq_of_norm_sub_le

theorem IsLimit.unique {E : CStarModule.{v, w} B} {u : ℕ → E.carrier} {y z : E.carrier}
    (hy : IsLimit E u y) (hz : IsLimit E u z) : y = z := by
  refine eq_of_norm_sub_le E fun ε hε => ?_
  obtain ⟨N₁, hN₁⟩ := hy (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hz (ε / 2) (half_pos hε)
  have h1 := hN₁ (max N₁ N₂) (le_max_left _ _)
  have h2 := hN₂ (max N₁ N₂) (le_max_right _ _)
  calc E.norm (y - z)
      ≤ E.norm (y - u (max N₁ N₂)) + E.norm (u (max N₁ N₂) - z) := modNorm_sub_le E _ _ _
    _ = E.norm (u (max N₁ N₂) - y) + E.norm (u (max N₁ N₂) - z) := by
      rw [modNorm_sub_comm E y (u (max N₁ N₂))]
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := add_halves ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsLimit.unique

theorem act_zero_right (E : CStarModule.{v, w} B) (x : E.carrier) : E.act x 0 = 0 := by
  have h := E.act_add_right x 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.act_zero_right

theorem act_smul_right (E : CStarModule.{v, w} B) (c : ℂ) (x : E.carrier) (b : B) :
    E.act x (c • b) = c • E.act x b := by
  refine E.eq_of_inner_eq fun y => ?_
  rw [E.inner_act_right, E.inner_smul_right, E.inner_act_right, mul_smul_comm]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.act_smul_right

/-- The inner product is continuous in its second slot. -/
theorem IsLimit.tendsto_inner_right {E : CStarModule.{v, w} B} {u : ℕ → E.carrier}
    {y : E.carrier} (h : IsLimit E u y) (x : E.carrier) :
    Tendsto (fun n => E.inner x (u n)) atTop (𝓝 (E.inner x y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : 0 < E.norm x + 1 := by linarith [E.norm_nonneg x]
  obtain ⟨N, hN⟩ := h (ε / 2 / (E.norm x + 1)) (div_pos (half_pos hε) hK)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, ← E.inner_sub_right]
  calc ‖E.inner x (u n - y)‖ ≤ E.norm x * E.norm (u n - y) := E.norm_inner_le _ _
    _ ≤ (E.norm x + 1) * (ε / 2 / (E.norm x + 1)) :=
      mul_le_mul (by linarith) (hN n hn) (E.norm_nonneg _) hK.le
    _ = ε / 2 := mul_div_cancel₀ _ hK.ne'
    _ < ε := half_lt_self hε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.IsLimit.tendsto_inner_right

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
