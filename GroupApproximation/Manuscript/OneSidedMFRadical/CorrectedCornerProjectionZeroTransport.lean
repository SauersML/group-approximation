import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerKazhdanQuadraticBridge

/-!
# Faithful transport of Kazhdan-projection vanishing

The universal-property step is stated for arbitrary C-star algebras and
bundled unitary representations.  It therefore never unfolds the large
universal-GNS corrected-corner representation.  A final small adapter relates
the generic predicate to `CorrectedCornerKazhdanProjectionZero`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter
open AbstractSpectralGap MaximalCStarKazhdanProjection
open PrintedCornerCompression

noncomputable section

universe u v w

/-- The maximal Kazhdan projection vanishes in every integrated lift of a
fixed unitary representation. -/
def KazhdanProjectionZeroForRepresentation
    {G : Type u} [Group G] {C : Type v} [CStarAlgebra C]
    (K : KazhdanData G) (rhoC : G →* unitary C) : Prop :=
  ∀ f : MaximalGroupCStar G →⋆ₐ[ℂ] C,
    (∀ g : G,
      f (maximalGroupCStarGenerator G g) = (rhoC g : C)) →
    f K.projection = 0

/-- A faithful star homomorphism transports ambient vanishing back to the
source representation. -/
theorem kazhdanProjectionZeroForRepresentation_of_faithfulTransport
    {G : Type u} [Group G] (K : KazhdanData G)
    {C : Type v} [CStarAlgebra C] {A : Type w} [CStarAlgebra A]
    (rhoC : G →* unitary C) (rhoA : G →* unitary A)
    (j : C →⋆ₐ[ℂ] A) (hj : Function.Injective j)
    (hrepresentation : (unitaryMap j).comp rhoC = rhoA)
    (F : MaximalGroupCStar G →⋆ₐ[ℂ] A)
    (hF : ∀ g : G,
      F (maximalGroupCStarGenerator G g) = (rhoA g : A))
    (hambientZero : F K.projection = 0) :
    KazhdanProjectionZeroForRepresentation K rhoC := by
  intro f hf
  have hcomp : j.comp f = F :=
    maximalGroupCStar_lift_unique G (j.comp f) F fun g ↦ by
      change j (f (maximalGroupCStarGenerator G g)) =
        F (maximalGroupCStarGenerator G g)
      rw [hf g]
      have hg := DFunLike.congr_fun hrepresentation g
      have hgcoe := congrArg (fun z : unitary A ↦ (z : A)) hg
      exact hgcoe.trans (hF g).symm
  apply hj
  calc
    j (f K.projection) = (j.comp f) K.projection := rfl
    _ = F K.projection := DFunLike.congr_fun hcomp K.projection
    _ = 0 := hambientZero
    _ = j 0 := (map_zero j).symm

/-- Ambient vanishing quantified over the prescribed representation chooses
the integrated ambient map internally. -/
theorem kazhdanProjectionZeroForRepresentation_of_faithfulGeneratorModel
    {G : Type u} [Group G] (K : KazhdanData G)
    {C : Type v} [CStarAlgebra C] {A : Type w} [CStarAlgebra A]
    (rhoC : G →* unitary C) (rhoA : G →* unitary A)
    (j : C →⋆ₐ[ℂ] A) (hj : Function.Injective j)
    (hrepresentation : (unitaryMap j).comp rhoC = rhoA)
    (hambientZero : ∀ F : MaximalGroupCStar G →⋆ₐ[ℂ] A,
      (∀ g : G,
        F (maximalGroupCStarGenerator G g) = (rhoA g : A)) →
      F K.projection = 0) :
    KazhdanProjectionZeroForRepresentation K rhoC := by
  obtain ⟨F, hF, _hunique⟩ :=
    maximalGroupCStar_existsUnique_lift_allUniverses G rhoA
  exact kazhdanProjectionZeroForRepresentation_of_faithfulTransport
    K rhoC rhoA j hj hrepresentation F hF (hambientZero F hF)

variable {G : Type} [Group G] {model : ℕ → FiniteModel}

/-- The small adapter from the generic transport predicate to the exact seam
consumed by the corrected-corner quadratic bridge. -/
theorem correctedCornerKazhdanProjectionZero_of_generic
    (D : PrintedCornerData G model) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (K : KazhdanData G)
    (hzero : KazhdanProjectionZeroForRepresentation K
      (correctedCornerOperatorUnitaryRepresentation D ω hω)) :
    CorrectedCornerKazhdanProjectionZero D ω hω K := by
  intro f hf
  apply hzero f
  intro g
  simpa only [correctedCornerOperator] using hf g

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
