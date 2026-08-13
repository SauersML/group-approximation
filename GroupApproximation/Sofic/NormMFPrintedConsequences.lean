import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.NormMFConsequences
import GroupApproximation.Sofic.NormMFCoronaRadical

/-!
# Printed consequences of norm-MF invisibility

This file gives exact wrappers for two statements in the manuscript's
consequences section: a nontrivial corona-invisible element obstructs every
faithful representation into a standard norm-matrix corona, and the
finite-normal compression criterion has the uniform finite-test-set form.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- A nontrivial element killed by every standard cofinite norm-matrix
corona representation rules out injectivity of each such representation. -/
theorem not_injective_of_coronaMFInvisible {x : G}
    (hx : CoronaMFInvisible x) (hne : x ≠ 1)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : G →* NormMatrixCoronaUnitary X) :
    ¬ Function.Injective rho := by
  intro hrho
  apply hne
  apply hrho
  rw [hx X hX rho, map_one]

namespace KazhdanCompressionCore

-- The finite-normal analytic core currently lives in Lean's base universe.
-- This is the same universe-polymorphic mathematical statement specialized
-- to the concrete countable groups used by the manuscript.
variable {Γ E : Type} [Group Γ] [Group E]

/-- **Uniform finite-normal invisibility.** Under exactly the finite-normal
compression hypotheses of the manuscript, every fixed element of the finite
normal subgroup is uniformly close to the identity in every sufficiently
multiplicative finite-dimensional unitary model. -/
theorem finiteNormal_uniform_invisibility
    [Countable E] (C : KazhdanCompressionCore Γ E)
    (F : Subgroup E) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal) {f₀ : E} (hf₀ : f₀ ∈ F) :
    ∀ ε : ℝ, 0 < ε → ∃ (δ : ℝ) (F₀ : Finset E), 0 < δ ∧
      ∀ (Y : FiniteModel) (φ : E → Matrix.unitaryGroup Y ℂ),
        (∀ g ∈ F₀, ∀ h ∈ F₀,
          ‖(φ g : Matrix Y Y ℂ) * φ h -
            (φ (g * h) : Matrix Y Y ℂ)‖ ≤ δ) →
        ‖(φ f₀ : Matrix Y Y ℂ) - 1‖ < ε := by
  intro ε hε
  obtain ⟨δ, F₀, hδ, huniform⟩ :=
    uniform_invisibility (C.finiteNormal_le_normMFResidual F hF hf₀) ε hε
  refine ⟨δ, F₀, hδ, ?_⟩
  intro Y φ hφ
  apply huniform Y φ
  intro g hg h hh
  calc
    ‖(φ (g * h) : Matrix Y Y ℂ) -
        (φ g : Matrix Y Y ℂ) * φ h‖ =
        ‖-((φ (g * h) : Matrix Y Y ℂ) -
          (φ g : Matrix Y Y ℂ) * φ h)‖ := (norm_neg _).symm
    _ = ‖(φ g : Matrix Y Y ℂ) * φ h -
        (φ (g * h) : Matrix Y Y ℂ)‖ := by rw [neg_sub]
    _ ≤ δ := hφ g hg h hh

end KazhdanCompressionCore
end GroupApproximation
