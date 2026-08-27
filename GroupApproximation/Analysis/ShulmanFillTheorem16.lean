import GroupApproximation.Analysis.ShulmanFillNormingFamily
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceCitations

/-!
# Shulman's Theorem 16, reduced to one norming statement

`Manuscript/MFRecognition/HNNPermanenceCitations.ShulmanTheorem16Statement` is
the printed criterion

> the full amalgamated free product `A₁ *_C A₂` of separable `C*`-algebras is
> MF as soon as there are injective `*`-homomorphisms `φ_A` and `φ_B` of `A₁`
> and `A₂` into one norm matrix corona with `φ_A ∘ ι_A = φ_B ∘ ι_B`.

This module proves that criterion from a single remaining input,
`CompatibleCoronaNormingStatement`: under exactly the hypotheses of Theorem
16, compatible representations of the amalgam with MF carriers are *norming*,
that is, they approximate the amalgam norm of every element.

Everything else in Theorem 16 is discharged here and in
`Analysis/ShulmanFillNormingFamily`:

* the universal amalgam of separable factors is separable;
* a norming family of MF-carrier representations, chosen diagonally over a
  dense sequence, evaluates the amalgam faithfully into the reduced product of
  the carriers;
* reduced products of MF algebras are MF
  (`Analysis/ReducedProductMFPermanence`).

So the analytic content that remains is exactly the norming statement: no
separability, quotient, or assembly step is left.  It is weaker than the
faithfulness of any single evaluation coordinate
(`ShulmanFill.norming_of_faithful_eval` derives it from faithfulness), which
is the form in which the symmetric-double argument of Shulman's proof is
usually stated.
-/

namespace GroupApproximation
namespace ShulmanFill

open Manuscript.MFRecognition

noncomputable section

/-- **The remaining input of Shulman's Theorem 16.**  Under the hypotheses of
the printed criterion — separable factors and one compatible pair of faithful,
possibly nonunital corona embeddings — the compatible representations of the
amalgam whose carriers are MF approximate the amalgam norm.

This is a statement about the *norm* of the full amalgam, which is the
supremum over all compatible representations: it says that the MF-carrier
coordinates already compute that supremum. -/
def CompatibleCoronaNormingStatement : Prop :=
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
              ∃ R : CStarAmalgamRepresentation iA iB,
                HasMFEmbedding R.carrier ∧
                  ‖x‖ - ε ≤ ‖universalCStarAmalgamEval iA iB R x‖

/-- **Shulman's Theorem 16 from the norming statement.**  With the norming
input, the printed criterion holds in the form consumed by
`Manuscript/MFRecognition/HNNPermanenceShulman`. -/
theorem shulmanTheorem16_of_compatibleCoronaNorming
    (hnorming : CompatibleCoronaNormingStatement) :
    HNNPermanence.ShulmanTheorem16Statement := by
  intro C A₁ A₂ _ _ _ iA iB _ hC hA₁ hA₂ Y _ phiA phiB hphiA hphiB hcomp
  haveI : TopologicalSpace.SeparableSpace A₁ := hA₁
  haveI : TopologicalSpace.SeparableSpace A₂ := hA₂
  exact isMFAlgebra_of_norming_representations iA iB
    (hnorming iA iB hC hA₁ hA₂ Y phiA phiB hphiA hphiB hcomp)

/-! ## The local form of the same input

The amalgam norm is the supremum of the norms of *all* evaluation
coordinates (`ShulmanFill.norm_eq_ciSup_universalCStarAmalgamEval`), so it is
enough to approximate one competing coordinate at a time.  That form mentions
no supremum and no dense sequence: it is the statement that an arbitrary
compatible pair of representations is approximated, on a single element, by a
compatible pair with an MF carrier. -/
def CompatibleCoronaDominationStatement : Prop :=
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
            ∀ (S : CStarAmalgamRepresentation iA iB)
              (x : UniversalCStarAmalgam iA iB) (ε : ℝ), 0 < ε →
              ∃ R : CStarAmalgamRepresentation iA iB,
                HasMFEmbedding R.carrier ∧
                  ‖universalCStarAmalgamEval iA iB S x‖ - ε ≤
                    ‖universalCStarAmalgamEval iA iB R x‖

/-- The local form implies the norming form. -/
theorem compatibleCoronaNorming_of_domination
    (hdom : CompatibleCoronaDominationStatement) :
    CompatibleCoronaNormingStatement := by
  intro C A₁ A₂ _ _ _ iA iB _ hC hA₁ hA₂ Y _ phiA phiB hphiA hphiB hcomp
  exact norming_of_dominating_representations iA iB
    (hdom iA iB hC hA₁ hA₂ Y phiA phiB hphiA hphiB hcomp)

/-- **Shulman's Theorem 16 from the local form of the input.** -/
theorem shulmanTheorem16_of_compatibleCoronaDomination
    (hdom : CompatibleCoronaDominationStatement) :
    HNNPermanence.ShulmanTheorem16Statement :=
  shulmanTheorem16_of_compatibleCoronaNorming
    (compatibleCoronaNorming_of_domination hdom)

end

end ShulmanFill
end GroupApproximation

#print axioms GroupApproximation.ShulmanFill.isMFAlgebra_of_norming_representations
#print axioms GroupApproximation.ShulmanFill.shulmanTheorem16_of_compatibleCoronaNorming
#print axioms GroupApproximation.ShulmanFill.shulmanTheorem16_of_compatibleCoronaDomination
