import GroupApproximation.Analysis.CompatibleCoronaSupportCorner
import GroupApproximation.Analysis.ShulmanFillTheorem16

/-!
# The remaining input of Theorem 16, at unital corona embeddings

`Analysis/ShulmanFillTheorem16` reduces Shulman's Theorem 16 to one norming
statement about the possibly *nonunital* corona embeddings of the printed
criterion.  Shulman's argument runs at unital embeddings, and
`Analysis/CompatibleCoronaSupportCorner` supplies exactly that passage: two
compatible faithful nonunital embeddings have the same support projection, so
one relabelled corner corona unitalizes both at once.

Composing the two, the whole of Theorem 16 rests on the norming statement for
*unital* compatible pairs, which is the form in which the symmetric-double
argument is carried out.

This module is deliberately not in the root import list: it depends on
`Analysis/CompatibleCoronaSupportCorner`, which is not yet wired there either.
Wiring the two together is a one-line change once that module lands.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-- **The remaining input of Theorem 16, at unital embeddings.**  Same as
`CompatibleCoronaNormingStatement`, except that the compatible corona
embeddings of the two factors are unital. -/
def UnitalCompatibleCoronaNormingStatement : Prop :=
  ∀ {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁]
    [CStarAlgebra A₂] (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
    [Nonempty (CStarAmalgamRepresentation iA iB)],
      TopologicalSpace.SeparableSpace C →
      TopologicalSpace.SeparableSpace A₁ →
      TopologicalSpace.SeparableSpace A₂ →
      ∀ (Z : ℕ → FiniteModel) [∀ n, Nonempty (Z n)]
        (phiA : A₁ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n))
        (phiB : A₂ →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ Z n)),
        Function.Injective phiA → Function.Injective phiB →
          phiA.comp iA = phiB.comp iB →
            ∀ (x : UniversalCStarAmalgam iA iB) (ε : ℝ), 0 < ε →
              ∃ R : CStarAmalgamRepresentation iA iB,
                HasMFEmbedding R.carrier ∧
                  ‖x‖ - ε ≤ ‖universalCStarAmalgamEval iA iB R x‖

/-- A factor of an amalgam that has at least one compatible representation is
nontrivial: the unit of the factor goes to the unit of a nontrivial carrier. -/
theorem nontrivial_left_of_nonempty_representation
    {C A₁ A₂ : Type} [CStarAlgebra C] [CStarAlgebra A₁] [CStarAlgebra A₂]
    (iA : C →⋆ₐ[ℂ] A₁) (iB : C →⋆ₐ[ℂ] A₂)
    [Nonempty (CStarAmalgamRepresentation iA iB)] : Nontrivial A₁ := by
  have R : CStarAmalgamRepresentation iA iB := Classical.arbitrary _
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h1
  have hzero : (1 : R.carrier) = 0 := by
    rw [← map_one R.left, h1, map_zero]
  exact one_ne_zero hzero

/-- The unital form of the norming input implies the nonunital one: pass to
the common support corner. -/
theorem compatibleCoronaNorming_of_unital
    (hunital : UnitalCompatibleCoronaNormingStatement) :
    CompatibleCoronaNormingStatement := by
  intro C A₁ A₂ _ _ _ iA iB _ hC hA₁ hA₂ Y _ phiA phiB hphiA hphiB hcomp
  haveI : Nontrivial A₁ := nontrivial_left_of_nonempty_representation iA iB
  obtain ⟨Z, hZ, phiA', phiB', hphiA', hphiB', hcomp'⟩ :=
    CompatibleCoronaSupportCorner.exists_compatible_injective_unital_supportCornerEmbeddings
      Y iA iB phiA phiB hphiA hphiB (by ext c; exact hcomp c)
  letI : ∀ n, Nonempty (Z n) := hZ
  exact hunital iA iB hC hA₁ hA₂ Z phiA' phiB' hphiA' hphiB' hcomp'

/-- **Shulman's Theorem 16 from the unital norming input.** -/
theorem shulmanTheorem16_of_unitalCompatibleCoronaNorming
    (hunital : UnitalCompatibleCoronaNormingStatement) :
    Manuscript.MFRecognition.HNNPermanence.ShulmanTheorem16Statement :=
  shulmanTheorem16_of_compatibleCoronaNorming
    (compatibleCoronaNorming_of_unital hunital)

end

end ShulmanFill
end GroupApproximation

#print axioms
  GroupApproximation.ShulmanFill.shulmanTheorem16_of_unitalCompatibleCoronaNorming
