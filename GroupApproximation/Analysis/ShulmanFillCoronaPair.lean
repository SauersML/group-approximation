import GroupApproximation.Analysis.ShulmanFillTheorem16
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

/-!
# The remaining input of Theorem 16, at corona pairs

`Analysis/ShulmanFillTheorem16` leaves one input,
`ShulmanFill.CompatibleCoronaNormingStatement`, phrased with an abstract
compatible representation whose carrier is only required to be MF.  The
analytic construction produces something more concrete: a unital compatible
pair of homomorphisms into one norm matrix corona.  This module carries the
input across that difference, so the remaining obligation mentions coronas
only.

The bridge is `normMatrixCorona_hasMFEmbedding_of_positive`: a norm corona
over any sequence of nonempty finite models has the bare MF embedding
property, so the compatible representation built from a corona pair by
`CStarAmalgamRepresentation.ofCompatiblePair` has an MF carrier by
construction.

This module is not in the root import list.  It was authored while builds
were suspended and has not been elaborated; keeping it unwired means a
mistake here cannot redden the root build, and the two modules it rests on
are both verified.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-- **The remaining input of Theorem 16, at corona pairs.**  Under the
hypotheses of the printed criterion, every element of the amalgam has its
norm approximated by the evaluation at a unital compatible pair of corona
homomorphisms.

Compared with `CompatibleCoronaNormingStatement` the carrier is no longer an
arbitrary MF algebra: it is a norm matrix corona, and the two factor maps are
the pair itself.  Nothing else changes. -/
def CoronaPairNormingStatement : Prop :=
  ∀ {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁]
    [CStarAlgebra A₂] (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
    [Nonempty (CStarAmalgamRepresentation iA iB)],
      TopologicalSpace.SeparableSpace C →
      TopologicalSpace.SeparableSpace A₁ →
      TopologicalSpace.SeparableSpace A₂ →
      ∀ (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
        (phiA : A₁ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n))
        (phiB : A₂ →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Y n)),
        Function.Injective phiA → Function.Injective phiB →
          (∀ c : C, phiA (iA c) = phiB (iB c)) →
            ∀ (x : UniversalCStarAmalgam iA iB) (ε : ℝ), 0 < ε →
              ∃ Z : ℕ → FiniteModel, ∃ hZ : ∀ n, Nonempty (Z n),
                letI : ∀ n, Nonempty (Z n) := hZ
                ∃ l : A₁ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
                  ∃ r : A₂ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n),
                    ∃ hlr : l.comp iA = r.comp iB,
                      ‖x‖ - ε ≤ ‖universalCStarAmalgamEval iA iB
                        (CStarAmalgamRepresentation.ofCompatiblePair
                          iA iB l r hlr) x‖

open Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit in
/-- A corona pair is a compatible representation with an MF carrier. -/
theorem hasMFEmbedding_ofCompatiblePair_corona
    {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁] [CStarAlgebra A₂]
    (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
    (Z : ℕ → FiniteModel) (hZ : ∀ n, Nonempty (Z n)) :
    letI : ∀ n, Nonempty (Z n) := hZ
    ∀ (l : A₁ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n))
      (r : A₂ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n))
      (hlr : l.comp iA = r.comp iB),
      HasMFEmbedding
        (CStarAmalgamRepresentation.ofCompatiblePair iA iB l r hlr).carrier := by
  letI : ∀ n, Nonempty (Z n) := hZ
  intro l r hlr
  exact normMatrixCorona_hasMFEmbedding_of_positive Z hZ

/-- The corona-pair input implies the abstract one. -/
theorem compatibleCoronaNorming_of_coronaPair
    (hpair : CoronaPairNormingStatement) :
    CompatibleCoronaNormingStatement := by
  intro C A₁ A₂ _ _ _ iA iB _ hC hA₁ hA₂ Y _ phiA phiB hphiA hphiB hcomp x ε hε
  obtain ⟨Z, hZ, l, r, hlr, hle⟩ :=
    hpair iA iB hC hA₁ hA₂ Y phiA phiB hphiA hphiB hcomp x ε hε
  letI : ∀ n, Nonempty (Z n) := hZ
  exact ⟨CStarAmalgamRepresentation.ofCompatiblePair iA iB l r hlr,
    hasMFEmbedding_ofCompatiblePair_corona iA iB Z hZ l r hlr, hle⟩

/-- **Shulman's Theorem 16 from the corona-pair input.** -/
theorem shulmanTheorem16_of_coronaPairNorming
    (hpair : CoronaPairNormingStatement) :
    Manuscript.MFRecognition.HNNPermanence.ShulmanTheorem16Statement :=
  shulmanTheorem16_of_compatibleCoronaNorming
    (compatibleCoronaNorming_of_coronaPair hpair)

end

end ShulmanFill
end GroupApproximation
