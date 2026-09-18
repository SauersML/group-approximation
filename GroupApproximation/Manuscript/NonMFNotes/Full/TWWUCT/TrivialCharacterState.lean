import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.TrivialCharacterFolner
import GroupApproximation.Analysis.GroupVonNeumannAlgebra

/-!
# The limit vector state of almost invariant vectors

Lane TWWUCT (work order WO-TWWCore-2), second step of Hulanicki's theorem.
Given almost invariant unit vectors `ξₙ ∈ ℓ²(G)`, the vector states
`ωₙ(T) = ⟪ξₙ, T ξₙ⟫` are bounded by `‖T‖`.  They converge along the ultrafilter
`Ultrafilter.of atTop`, by compactness of closed balls in `ℂ`.  The limit `ω` is
a state on `B(ℓ²(G))` with `ω(1) = 1` and `ω(T⋆) = conj ω(T)`.  Asymptotic
invariance gives `ω(S λ_g) = ω(S)` and `ω(λ_g S) = ω(S)`.

* `vectorState`, `vectorState_apply`, `norm_vectorState_le`.
* `AlmostInvariantVectors.limitState` with `limitState_one`, `limitState_star`.
* `limitState_mul_leftRegular`, `limitState_leftRegular_mul`.
-/

namespace GroupApproximation.Full.TWWUCT

open Filter Topology ReducedGroupCStarTrace
open scoped InnerProductSpace

universe u

variable {G : Type u} [Group G]

/-- The vector state `T ↦ ⟪ξ, T ξ⟫` on `B(ℓ²(G))`. -/
noncomputable def vectorState (ξ : GroupHilbert G) :
    (GroupHilbert G →L[ℂ] GroupHilbert G) →L[ℂ] ℂ :=
  (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ (GroupHilbert G) ξ)

theorem vectorState_apply (ξ : GroupHilbert G) (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    vectorState ξ T = ⟪ξ, T ξ⟫_ℂ := by
  rw [vectorState, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply]

theorem norm_vectorState_le {ξ : GroupHilbert G} (hξ : ‖ξ‖ = 1)
    (T : GroupHilbert G →L[ℂ] GroupHilbert G) : ‖vectorState ξ T‖ ≤ ‖T‖ := by
  rw [vectorState_apply]
  calc ‖⟪ξ, T ξ⟫_ℂ‖ ≤ ‖ξ‖ * ‖T ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖T‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left (T.le_opNorm ξ) (norm_nonneg _)
    _ = ‖T‖ := by rw [hξ, one_mul, mul_one]

theorem vectorState_star (ξ : GroupHilbert G) (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    vectorState ξ (star T) = star (vectorState ξ T) := by
  rw [vectorState_apply, vectorState_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← starRingEnd_apply, inner_conj_symm]

theorem leftRegularOperator_apply_eq (g : G) (x : GroupHilbert G) :
    leftRegularOperator G g x = leftRegular G g x :=
  rfl

/-- The ultrafilter on `ℕ` along which the vector states are taken to converge. -/
noncomputable abbrev natUltrafilter : Ultrafilter ℕ :=
  Ultrafilter.of atTop

/-- A bounded complex sequence converges along an ultrafilter. -/
theorem exists_tendsto_ultrafilter (U : Ultrafilter ℕ) {f : ℕ → ℂ} {C : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ C) : ∃ z, Tendsto f (U : Filter ℕ) (𝓝 z) := by
  have hle : ((U.map f : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓟 (Metric.closedBall (0 : ℂ) C) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    exact Filter.univ_mem' fun n ↦ by simpa using hf n
  obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds _ hle
  exact ⟨z, by rwa [Ultrafilter.coe_map] at hz⟩

namespace AlmostInvariantVectors

variable (V : AlmostInvariantVectors G)

/-- The ultralimit of the vector states. -/
noncomputable def limitFun (T : GroupHilbert G →L[ℂ] GroupHilbert G) : ℂ :=
  limUnder (natUltrafilter : Filter ℕ) fun n ↦ vectorState (V.vec n) T

theorem tendsto_limitFun (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    Tendsto (fun n ↦ vectorState (V.vec n) T) (natUltrafilter : Filter ℕ)
      (𝓝 (V.limitFun T)) :=
  tendsto_nhds_limUnder
    (exists_tendsto_ultrafilter _ fun n ↦ norm_vectorState_le (V.norm_vec n) T)

/-- The limit state, a continuous linear functional of norm at most one. -/
noncomputable def limitState : (GroupHilbert G →L[ℂ] GroupHilbert G) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := V.limitFun
      map_add' := fun S T ↦ tendsto_nhds_unique (V.tendsto_limitFun (S + T))
        (((V.tendsto_limitFun S).add (V.tendsto_limitFun T)).congr fun n ↦ by
          rw [map_add])
      map_smul' := fun c T ↦ by
        rw [RingHom.id_apply, smul_eq_mul]
        exact tendsto_nhds_unique (V.tendsto_limitFun (c • T))
          (((V.tendsto_limitFun T).const_mul c).congr fun n ↦ by
            rw [map_smul, smul_eq_mul]) }
    1 fun T ↦ by
      rw [one_mul]
      exact le_of_tendsto' (V.tendsto_limitFun T).norm fun n ↦
        norm_vectorState_le (V.norm_vec n) T

theorem limitState_apply (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    V.limitState T = V.limitFun T :=
  rfl

theorem tendsto_limitState (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    Tendsto (fun n ↦ vectorState (V.vec n) T) (natUltrafilter : Filter ℕ)
      (𝓝 (V.limitState T)) :=
  V.tendsto_limitFun T

theorem limitState_one : V.limitState 1 = 1 := by
  refine tendsto_nhds_unique (V.tendsto_limitState 1)
    (tendsto_const_nhds.congr fun n ↦ ?_)
  rw [vectorState_apply, one_apply_eq_self, inner_self_eq_norm_sq_to_K, V.norm_vec n]
  simp

theorem limitState_star (T : GroupHilbert G →L[ℂ] GroupHilbert G) :
    V.limitState (star T) = star (V.limitState T) :=
  tendsto_nhds_unique (V.tendsto_limitState (star T))
    ((V.tendsto_limitState T).star.congr fun n ↦ (vectorState_star _ T).symm)

/-- If `ωₙ(S) - ωₙ(T) → 0` then `ω(S) = ω(T)`. -/
theorem limitState_eq_of_tendsto_sub {S T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (h : Tendsto (fun n ↦ vectorState (V.vec n) S - vectorState (V.vec n) T) atTop (𝓝 0)) :
    V.limitState S = V.limitState T := by
  have hU := (V.tendsto_limitState T).add (h.mono_left (Ultrafilter.of_le atTop))
  rw [add_zero] at hU
  exact tendsto_nhds_unique (V.tendsto_limitState S) (hU.congr fun n ↦ by ring)

theorem limitState_mul_leftRegular (S : GroupHilbert G →L[ℂ] GroupHilbert G) (g : G) :
    V.limitState (S * leftRegularOperator G g) = V.limitState S := by
  have hb : Tendsto (fun n ↦ ‖S‖ * ‖leftRegular G g (V.vec n) - V.vec n‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (V.tendsto g).const_mul ‖S‖
  refine V.limitState_eq_of_tendsto_sub (squeeze_zero_norm (fun n ↦ ?_) hb)
  rw [vectorState_apply, vectorState_apply, ← inner_sub_right, mul_apply_eq_comp, ← map_sub,
    leftRegularOperator_apply_eq]
  calc ‖⟪V.vec n, S (leftRegular G g (V.vec n) - V.vec n)⟫_ℂ‖
      ≤ ‖V.vec n‖ * ‖S (leftRegular G g (V.vec n) - V.vec n)‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖S‖ * ‖leftRegular G g (V.vec n) - V.vec n‖) := by
      rw [V.norm_vec n]
      exact mul_le_mul_of_nonneg_left (S.le_opNorm _) zero_le_one
    _ = ‖S‖ * ‖leftRegular G g (V.vec n) - V.vec n‖ := one_mul _

theorem leftRegularOperator_eq_adjoint (g : G) :
    leftRegularOperator G g = ContinuousLinearMap.adjoint (leftRegularOperator G g⁻¹) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, GroupVonNeumann.star_leftRegularOperator, inv_inv]

theorem limitState_leftRegular_mul (S : GroupHilbert G →L[ℂ] GroupHilbert G) (g : G) :
    V.limitState (leftRegularOperator G g * S) = V.limitState S := by
  have hb : Tendsto (fun n ↦ ‖S‖ * ‖leftRegular G g⁻¹ (V.vec n) - V.vec n‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (V.tendsto g⁻¹).const_mul ‖S‖
  refine V.limitState_eq_of_tendsto_sub (squeeze_zero_norm (fun n ↦ ?_) hb)
  rw [vectorState_apply, vectorState_apply, mul_apply_eq_comp, leftRegularOperator_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ← inner_sub_left, leftRegularOperator_apply_eq]
  calc ‖⟪leftRegular G g⁻¹ (V.vec n) - V.vec n, S (V.vec n)⟫_ℂ‖
      ≤ ‖leftRegular G g⁻¹ (V.vec n) - V.vec n‖ * ‖S (V.vec n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖leftRegular G g⁻¹ (V.vec n) - V.vec n‖ * (‖S‖ * 1) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖S (V.vec n)‖ ≤ ‖S‖ * ‖V.vec n‖ := S.le_opNorm _
        _ = ‖S‖ * 1 := by rw [V.norm_vec n]
    _ = ‖S‖ * ‖leftRegular G g⁻¹ (V.vec n) - V.vec n‖ := by ring

end AlmostInvariantVectors

end GroupApproximation.Full.TWWUCT
