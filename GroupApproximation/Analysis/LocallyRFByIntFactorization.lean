import GroupApproximation.Analysis.LocallyRFByIntAction
import GroupApproximation.Analysis.AmenableTraceGeneratorDense

/-!
# Amenability of the canonical trace for locally RF-by-integer groups

This file assembles the finite-window construction.  At stage `n` we test the
first `n + 1` ambient group elements, use `n + 1` cyclic levels, and choose one
finite quotient separating all nontrivial normal coordinates visible in that
window.  The associated quasi-regular compressions are exactly trace-correct
on every eventually tested generator.  Their generator-pair Hilbert--Schmidt
defects are bounded by the square root of the cyclic boundary ratio.
-/

namespace GroupApproximation
namespace LocallyRFByIntFactorization

open Filter Matrix Quasidiagonal ResidualFinitePacket
open LocallyRFByIntAmenableTrace LocallyRFByIntSchedule
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G N : Type} [Group G] [Group N] [Countable G]
variable (α : Multiplicative ℤ →* MulAut N)
variable (e : G ≃* (N ⋊[α] Multiplicative ℤ))

/-! ## The stage packet and its compression -/

/-- The ambient elements tested at stage `n`. -/
abbrev stageWindow (n : ℕ) : Finset G :=
  exhaustion G 1 n

/-- The honest integer representatives of the cyclic levels at stage `n`. -/
abbrev stageLevelWindow (n : ℕ) : Finset ℤ :=
  LocallyRFByIntAmenableTrace.levelWindow (levelSize n)

/-- One finite quotient simultaneously separating all nontrivial normal
coordinates visible at stage `n`. -/
noncomputable def stagePacket
    (hN : IsLocallyResiduallyFinite N) (n : ℕ) :
    Packet (normalWindowSubgroup α e (stageWindow n) (stageLevelWindow n))
      (nontrivialNormalWindow α e (stageWindow n) (stageLevelWindow n)) :=
  Classical.choice
    (exists_normalWindow_packet α e hN (stageWindow n) (stageLevelWindow n))

/-- The finite matrix index set at stage `n`. -/
abbrev stageModel (hN : IsLocallyResiduallyFinite N) (n : ℕ) : FiniteModel :=
  cyclicWindowModel (stagePacket α e hN n) (levelSize n)

/-- The unital completely positive compression at stage `n`. -/
noncomputable def stageMap (hN : IsLocallyResiduallyFinite N) (n : ℕ) :
    MaximalGroupCStar G →ₗ[ℂ]
      Matrix (stageModel α e hN n) (stageModel α e hN n) ℂ :=
  windowCompression α e (stagePacket α e hN n) (levelSize n)

theorem stageMap_one (hN : IsLocallyResiduallyFinite N) (n : ℕ) :
    stageMap α e hN n 1 = 1 :=
  windowCompression_one α e (stagePacket α e hN n) (levelSize n)

theorem stageMap_completelyPositive (hN : IsLocallyResiduallyFinite N)
    (n : ℕ) :
    IsCompletelyPositiveOnMatrices (stageModel α e hN n)
      ⇑(stageMap α e hN n) :=
  windowCompression_completelyPositive α e (stagePacket α e hN n)
    (levelSize n)

theorem norm_stageMap_le (hN : IsLocallyResiduallyFinite N) (n : ℕ)
    (a : MaximalGroupCStar G) :
    ‖stageMap α e hN n a‖ ≤ ‖a‖ :=
  norm_windowCompression_le α e (stagePacket α e hN n) (levelSize n) a

/-! ## Boundary control -/

/-- Away from cyclic wrap-around, translating by a tested element remains in
the selected coset window. -/
theorem stage_translate_mem_range_of_not_boundary
    (hN : IsLocallyResiduallyFinite N) (n : ℕ) {g : G}
    (hg : g ∈ stageWindow n) (x : stageModel α e hN n)
    (hx : x.1 ∉ boundaryLevels (levelSize n) (height α e g)) :
    g • cyclicWindowCoset α e (stagePacket α e hN n) (levelSize n) x ∈
      Set.range
        (cyclicWindowCoset α e (stagePacket α e hN n) (levelSize n)) := by
  have hlevel :
      ((x.1.val : ℤ) + height α e g) ∈ stageLevelWindow n := by
    rw [← val_add_eq_of_not_boundary hx]
    exact zmod_val_mem_levelWindow (levelSize n)
      (x.1 + (height α e g : ZMod (levelSize n)))
  apply smul_cyclicWindowCoset_mem_range_of_not_boundary α e
    (stagePacket α e hN n) (levelSize n) g x hx
  exact normalWindow_subset_subgroup α e (stageWindow n) (stageLevelWindow n)
    (normalCoordinate_mem_normalWindow α e hg hlevel)

/-- At a stage testing `h`, every generator-pair defect is bounded by the
square root of the boundary fraction for the height of `h`. -/
theorem hsNorm_stage_generatorDefect_le
    (hN : IsLocallyResiduallyFinite N) (n : ℕ) (g h : G)
    (hh : h ∈ stageWindow n) :
    hsNorm (stageModel α e hN n)
        (stageMap α e hN n (maximalGroupCStarGenerator G (g * h)) -
          stageMap α e hN n (maximalGroupCStarGenerator G g) *
            stageMap α e hN n (maximalGroupCStarGenerator G h)) ≤
      Real.sqrt (boundaryRatio (height α e h) n) := by
  let P := stagePacket α e hN n
  let L := levelSize n
  have hraw := hsNorm_windowCompression_generatorDefect_le α e P L g h
  have hinside : ∀ x : cyclicWindowModel P L,
      x.1 ∉ boundaryLevels L (height α e h) →
        h • cyclicWindowCoset α e P L x ∈
          Set.range (cyclicWindowCoset α e P L) := by
    intro x hx
    exact stage_translate_mem_range_of_not_boundary α e hN n hh x hx
  have hcard := card_escape_le_boundary α e P L h hinside
  have hcardR :
      ((QuasiRegularCompression.escape (ambientPacketSubgroup α e P)
        (cyclicWindowModel P L) (cyclicWindowCoset α e P L) h).card : ℝ) ≤
        ((boundaryLevels L (height α e h)).card *
          Fintype.card P.quotientModel : ℕ) := by
    exact_mod_cast hcard
  have hmodelCard :
      (Fintype.card (cyclicWindowModel P L) : ℝ) =
        (L : ℝ) * (Fintype.card P.quotientModel : ℝ) := by
    rw [card_cyclicWindowModel]
    push_cast
    rfl
  have hmodelPos : 0 < (Fintype.card (cyclicWindowModel P L) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (cyclicWindowModel P L))
  have hLPos : 0 < (L : ℝ) := by
    exact_mod_cast levelSize_pos n
  have hratio :
      ((QuasiRegularCompression.escape (ambientPacketSubgroup α e P)
          (cyclicWindowModel P L) (cyclicWindowCoset α e P L) h).card : ℝ) /
          Fintype.card (cyclicWindowModel P L) ≤
        ((boundaryLevels L (height α e h)).card : ℝ) / L := by
    apply (div_le_div_iff₀ hmodelPos hLPos).2
    rw [hmodelCard]
    have hmul := mul_le_mul_of_nonneg_right hcardR (show 0 ≤ (L : ℝ) by positivity)
    simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hmul
  calc
    _ ≤ Real.sqrt
        (((QuasiRegularCompression.escape (ambientPacketSubgroup α e P)
          (cyclicWindowModel P L) (cyclicWindowCoset α e P L) h).card : ℝ) /
            Fintype.card (cyclicWindowModel P L)) := hraw
    _ ≤ Real.sqrt (((boundaryLevels L (height α e h)).card : ℝ) / L) :=
      Real.sqrt_le_sqrt hratio
    _ = Real.sqrt (boundaryRatio (height α e h) n) := by
      rfl

/-- Generator-pair multiplicative defects tend to zero. -/
theorem tendsto_stage_generator_mul_hs
    (hN : IsLocallyResiduallyFinite N) (g h : G) :
    Tendsto (fun n ↦ hsNorm (stageModel α e hN n)
      (stageMap α e hN n
          (maximalGroupCStarGenerator G g * maximalGroupCStarGenerator G h) -
        stageMap α e hN n (maximalGroupCStarGenerator G g) *
          stageMap α e hN n (maximalGroupCStarGenerator G h)))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun n ↦ Real.sqrt (boundaryRatio (height α e h) n))
  · exact Eventually.of_forall fun n ↦ hsNorm_nonneg _ _
  · filter_upwards [eventually_eventually_mem_exhaustion G 1 h] with n hn
    simpa only [maximalGroupCStarGenerator_mul] using
      (hsNorm_stage_generatorDefect_le α e hN n g h hn)
  · exact tendsto_sqrt_boundaryRatio (height α e h)

/-! ## Exact traces on tested generators -/

theorem stage_generator_trace_eq_zero
    (hN : IsLocallyResiduallyFinite N) (n : ℕ) {g : G}
    (hgF : g ∈ stageWindow n) (hg : g ≠ 1) :
    normTrace (stageModel α e hN n)
      (stageMap α e hN n (maximalGroupCStarGenerator G g)) = 0 := by
  by_cases hg0 : height α e g = 0
  · exact normTrace_windowCompression_generator_eq_zero_of_mem α e
      (stageWindow n) (levelSize n) (stagePacket α e hN n) hgF hg hg0
  · exact normTrace_windowCompression_generator_of_height_ne_zero α e
      (stagePacket α e hN n) (levelSize n) g hg0

/-- The normalized traces of the stage compressions converge to the canonical
trace on every canonical group generator. -/
theorem tendsto_stage_generator_trace
    (hN : IsLocallyResiduallyFinite N) (g : G) :
    Tendsto (fun n ↦
      ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g) -
        normTrace (stageModel α e hN n)
          (stageMap α e hN n (maximalGroupCStarGenerator G g))‖)
      atTop (nhds 0) := by
  by_cases hg : g = 1
  · subst g
    have hgen : maximalGroupCStarGenerator G 1 = 1 :=
      congrArg (fun w : unitary (MaximalGroupCStar G) ↦
        (w : MaximalGroupCStar G))
        (map_one (maximalGroupCStarUnitaryHom G))
    have hzero : ∀ n : ℕ,
        ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G 1) -
          normTrace (stageModel α e hN n)
            (stageMap α e hN n (maximalGroupCStarGenerator G 1))‖ = 0 := by
      intro n
      rw [canonicalMaximalTrace_generator_one, hgen, stageMap_one,
        normTrace_one' (stageModel α e hN n) Fintype.card_pos, sub_self, norm_zero]
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  · have heq : ∀ᶠ n in atTop,
        ‖canonicalMaximalTrace G (maximalGroupCStarGenerator G g) -
          normTrace (stageModel α e hN n)
            (stageMap α e hN n (maximalGroupCStarGenerator G g))‖ = 0 := by
      filter_upwards [eventually_eventually_mem_exhaustion G 1 g] with n hn
      rw [canonicalMaximalTrace_generator_of_ne_one G hg,
        stage_generator_trace_eq_zero α e hN n hn hg, sub_self, norm_zero]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)

/-! ## The generic factorization theorem -/

/-- If `G` is countable and isomorphic to a semidirect product of a locally
residually finite group by `ℤ`, then its canonical maximal trace is amenable. -/
theorem canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt
    (α : Multiplicative ℤ →* MulAut N)
    (e : G ≃* (N ⋊[α] Multiplicative ℤ))
    (hN : IsLocallyResiduallyFinite N) :
    IsAmenableTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) := by
  refine ⟨amenableTraceModel_of_dense_generators
    (stageMap α e hN) (stageMap_one α e hN)
    (stageMap_completelyPositive α e hN) (norm_stageMap_le α e hN)
    (canonicalMaximalTrace G) (Set.range (maximalGroupCStarGenerator G))
    (maximalGroupCStar_dense_span_generator G) ?_ ?_⟩
  · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    exact tendsto_stage_generator_mul_hs α e hN g h
  · rintro _ ⟨g, rfl⟩
    exact tendsto_stage_generator_trace α e hN g

#audit_axioms
  canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt

end

end LocallyRFByIntFactorization
end GroupApproximation
