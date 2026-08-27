import GroupApproximation.Manuscript.MFRecognition.HNNPermanence
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceShulman
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronization

/-!
# `thm:hnn-permanence` from its two citations

`HNNInputs` bundles the one analytic statement the HNN permanence proof does
not prove in-repo: that the universal `C*`-HNN algebra `U` is MF.  The printed
proof obtains it from two cited theorems, Ueda's corner identification
(`[Ueda, Proposition 2.4]`, named `UedaCornerMapStatement`) and Shulman's
amalgam criterion (`[Shulman, Theorem 16]`, named
`ShulmanTheorem16Statement`); `HNNPermanenceShulman` already derives the
statement from the two.  This module closes the loop: the bundle is built from
the two citations, and every printed form of `thm:hnn-permanence` and
`cor:central-hnn` is restated with the two citations as its only inputs.

The tensor-synchronization bundle `TensorSynchronization.HNNPermanenceInputs`
consumed by `lem:positive-branch` is built from the same two citations, so the
positive branch, and with it the whole recognition family, rests on exactly
these two literature statements on the analytic side.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

noncomputable section

/-- **Ueda's corner map and Shulman's amalgam theorem discharge the HNN
permanence bundle.** -/
def hnnInputs_of_citations (hShulman : ShulmanTheorem16Statement)
    (hUeda : UedaCornerMapStatement) : HNNInputs :=
  ⟨universalHNNIsMFStatement_of_shulman hShulman hUeda⟩

/-- **`thm:hnn-permanence`**, with the two citations as its only inputs. -/
theorem manuscriptHNNPermanence_of_citations
    (hShulman : ShulmanTheorem16Statement) (hUeda : UedaCornerMapStatement)
    {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) :
    IsRegularlyRealized (HNNExtension G S T phi) :=
  manuscriptHNNPermanence (hnnInputs_of_citations hShulman hUeda) phi
    realization iota hiota W hW

/-- **`thm:hnn-permanence`, second sentence**, from the two citations. -/
theorem manuscriptHNNPermanence_isOperatorMF_of_citations
    (hShulman : ShulmanTheorem16Statement) (hUeda : UedaCornerMapStatement)
    {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota)
    (W : unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (hW : ∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) :
    IsOperatorMF (HNNExtension G S T phi) :=
  manuscriptHNNPermanence_isOperatorMF (hnnInputs_of_citations hShulman hUeda)
    phi realization iota hiota W hW

/-- **`cor:central-hnn`**, from the two citations. -/
theorem manuscriptCentralHNN_of_citations
    (hShulman : ShulmanTheorem16Statement) (hUeda : UedaCornerMapStatement)
    {G : Type} [Group G] [Countable G]
    {S : Subgroup G}
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (hiota : Function.Injective iota) :
    IsRegularlyRealized (HNNExtension G S S (MulEquiv.refl S)) :=
  manuscriptHNNPermanence (hnnInputs_of_citations hShulman hUeda)
    (MulEquiv.refl S) realization iota hiota 1 (fun s => by simp)

/-- **The bundle `lem:tensor-sync` consumes**, built from the two
citations. -/
theorem hnnPermanenceInputs_of_citations
    (hShulman : ShulmanTheorem16Statement) (hUeda : UedaCornerMapStatement) :
    TensorSynchronization.HNNPermanenceInputs where
  hnnPermanence := by
    intro G _ _ S T phi A _ realization X _ iota hiota W hW
    exact manuscriptHNNPermanence (hnnInputs_of_citations hShulman hUeda) phi
      realization iota hiota W hW

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
