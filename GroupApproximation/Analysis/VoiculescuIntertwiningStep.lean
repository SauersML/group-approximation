import GroupApproximation.Analysis.VoiculescuIntertwiningDefect
import GroupApproximation.Analysis.VoiculescuFrameFromGlimm

/-!
# (V4) The finite-dimensional intertwining step

`Analysis/VoiculescuOneStep` gives the one-step approximation in compression
form, and `Analysis/VoiculescuIntertwiningDefect` exchanges three compressions
for one intertwining bound.  This module puts the two together: the statement
below is the one-step approximation with `V⋆σ(a)V - ρ(a)` replaced by
`σ(a)V - Vρ(a)`, and it is proved outright from `OneStepApproximationStatement`.

That is the whole of what (V4) inherits from (V3).  What (V4) still owes is the
passage from a finite-dimensional representation space to a separable one, and
from small defects to compact ones — the iteration along a dense sequence with
mutually orthogonal ranges.  Neither is here.

## The two costs of the exchange

The finite set has to be enlarged to be closed under `a ↦ a⋆` and `a ↦ a⋆a`,
because the identity behind the exchange uses all three compressions; and the
tolerance has to be squared, because the identity bounds `‖X‖²` rather than
`‖X‖`.  Running the compression form at `ε²/(2(1 + 2M))`, with `M` a bound for
`‖ρ(a)‖` on the finite set, leaves the intertwining defect below `ε`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace

noncomputable section

/-- **(V4a) The finite-dimensional intertwining step.**  The one-step
approximation, with the compression defect replaced by the intertwining defect
the assembly consumes. -/
def IntertwiningStepStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)), IsClosed (A : Set (H →L[ℂ] H)) →
      (∀ T ∈ A, IsCompactOperator T → T = 0) →
      ∀ (K₀ : Type) [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
        [FiniteDimensional ℂ K₀] [CompleteSpace K₀]
        (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) (F : Finset ↥A) (eps : ℝ), 0 < eps →
          ∀ V : Submodule ℂ H, FiniteDimensional ℂ V →
            ∃ W : K₀ →L[ℂ] H,
              ContinuousLinearMap.adjoint W ∘L W = 1 ∧
              (∀ x, W x ∈ Vᗮ) ∧
              ∀ a ∈ F, ‖(a : H →L[ℂ] H) ∘L W - W ∘L rho a‖ < eps

/-- **The intertwining step from the compression step.** -/
theorem intertwiningStep_of_oneStep (h : OneStepApproximationStatement) :
    IntertwiningStepStatement := by
  classical
  intro H _ _ _ A hAclosed hAK K₀ _ _ _ _ rho F eps heps V hV
  set M : ℝ := ∑ a ∈ F, ‖rho a‖ with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun a _ ↦ norm_nonneg _
  have hden : (0:ℝ) < 2 * (1 + 2 * M) := by linarith
  set d : ℝ := eps ^ 2 / (2 * (1 + 2 * M)) with hddef
  have hd0 : 0 < d := div_pos (by positivity) hden
  have hdM : d * (1 + 2 * M) = eps ^ 2 / 2 := by
    rw [hddef]
    field_simp
  set F' : Finset ↥A :=
    (F ∪ F.image star) ∪ F.image (fun a ↦ star a * a) with hF'def
  obtain ⟨W, hWiso, hWV, hWF⟩ := h H A hAclosed hAK K₀ rho F' d hd0 V hV
  refine ⟨W, hWiso, hWV, ?_⟩
  intro a ha
  have hmem1 : star a * a ∈ F' :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)
  have hmem2 : star a ∈ F' :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
  have hmem3 : a ∈ F' :=
    Finset.mem_union_left _ (Finset.mem_union_left _ ha)
  have hsq := norm_intertwine_sq_le_of_compress rho W hWiso a
    (hWF _ hmem1).le (hWF _ hmem2).le (hWF _ hmem3).le
  have hMa : ‖rho a‖ ≤ M :=
    Finset.single_le_sum (f := fun b ↦ ‖rho b‖) (fun i _ ↦ norm_nonneg _) ha
  have hle : ‖(a : H →L[ℂ] H) ∘L W - W ∘L rho a‖ ^ 2 ≤ eps ^ 2 / 2 := by
    refine hsq.trans ?_
    rw [← hdM]
    exact mul_le_mul_of_nonneg_left (by linarith) hd0.le
  by_contra hcon
  rw [not_lt] at hcon
  have h5 : eps * eps
      ≤ ‖(a : H →L[ℂ] H) ∘L W - W ∘L rho a‖ * ‖(a : H →L[ℂ] H) ∘L W - W ∘L rho a‖ :=
    mul_le_mul hcon hcon heps.le (le_trans heps.le hcon)
  nlinarith [hle, h5, heps]

/-- **(V4a) closed against Glimm's lemma**, through the one-step approximation. -/
theorem intertwiningStep_of_glimm (hG : GlimmLemmaStatement) :
    IntertwiningStepStatement :=
  intertwiningStep_of_oneStep (oneStepApproximation_of_glimm hG)

end

end ShulmanFill
end GroupApproximation
