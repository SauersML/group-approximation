import GroupApproximation.Analysis.CStarCorner
import GroupApproximation.Analysis.UniversalCStarAmalgam
import GroupApproximation.Meta.AxiomGuard

/-!
# Algebraic sentences in the HNN-amalgam corner argument

This file isolates the parts of the proof of `thm:hnn-permanence` that do not
use the MF permanence theorem for full amalgamated free products.  It proves:

* faithfulness of the two canonical factor maps when one compatible
  representation is faithful on both factors;
* equality of the two images of the amalgamated algebra;
* the matrix-unit calculation showing that `e₁₂ f₂₁` is unitary in the
  `ePe` corner;
* injectivity of a homomorphism admitting the printed matrix retraction; and
* heredity of the MF property through the corner and an injective map into it.

The compatible-corona MF criterion itself is not assumed here.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace HNNAmalgamCornerSentences

open scoped CStarAlgebra

noncomputable section

universe u v w

/-! ## The universal amalgam -/

/-- Sentence `ce5f1d31a90e`, in the exact abstract form used in the proof:
one compatible representation faithful on both factors makes both canonical
factor maps into the universal full amalgam injective. -/
theorem manuscriptSentence_ce5f1d31a90e_factorMapsInjective
    {C A B : Type u} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)]
    (R : CStarAmalgamRepresentation iA iB)
    (hleft : Function.Injective R.left)
    (hright : Function.Injective R.right) :
    Function.Injective (universalCStarAmalgamLeft iA iB) ∧
      Function.Injective (universalCStarAmalgamRight iA iB) :=
  ⟨universalCStarAmalgamLeft_injective_of_coordinate iA iB R hleft,
    universalCStarAmalgamRight_injective_of_coordinate iA iB R hright⟩

/-- Sentence `68cf3b4da8ab`, before specializing to the two diagonal matrix
units: the canonical factor maps have the same value on every element of the
amalgamated algebra. -/
theorem manuscriptSentence_68cf3b4da8ab_commonImage
    {C A B : Type u} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
    (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    [Nonempty (CStarAmalgamRepresentation iA iB)] (c : C) :
    universalCStarAmalgamLeft iA iB (iA c) =
      universalCStarAmalgamRight iA iB (iB c) := by
  exact congrArg
    (fun f : C →⋆ₐ[ℂ] UniversalCStarAmalgam iA iB ↦ f c)
    (universalCStarAmalgam_compatible iA iB)

/-! ## The corner word -/

/-- Sentence `6e8a0c1082a2`: the matrix-unit identities used in the paper
imply that `e₁₂ f₂₁` is a unitary in the corner with unit `e`.

The hypotheses are precisely the individual matrix-unit products and star
relations used in the two displayed calculations; no analytic or literature
input occurs in this lemma. -/
theorem manuscriptSentence_6e8a0c1082a2_cornerWordUnitary
    {P : Type u} [CStarAlgebra P]
    (e e12 e21 e22 f12 f21 f22 : P)
    (he_star : star e = e) (he_mul : e * e = e)
    (hstar_e12 : star e12 = e21)
    (hstar_f21 : star f21 = f12)
    (he_e12 : e * e12 = e12)
    (hf21_e : f21 * e = f21)
    (hf21_f12 : f21 * f12 = f22)
    (he12_e22 : e12 * e22 = e12)
    (he12_e21 : e12 * e21 = e)
    (he21_e12 : e21 * e12 = e22)
    (hf12_f22 : f12 * f22 = f12)
    (hf12_f21 : f12 * f21 = e)
    (he22_f22 : e22 = f22) :
    ∃ w : unitary (CStarCorner e he_star he_mul),
      ((w : CStarCorner e he_star he_mul) : P) = e12 * f21 := by
  let x : P := e12 * f21
  have hx_left : e * x = x := by
    simp only [x, ← mul_assoc, he_e12]
  have hx_right : x * e = x := by
    simp only [x, mul_assoc, hf21_e]
  let xc : CStarCorner e he_star he_mul := ⟨x, hx_left, hx_right⟩
  have hstar_x : star x = f12 * e21 := by
    simp only [x, star_mul, hstar_f21, hstar_e12]
  have hstar_mul : star x * x = e := by
    calc
      star x * x = (f12 * e21) * (e12 * f21) := by rw [hstar_x]
      _ = f12 * (e21 * e12) * f21 := by simp only [mul_assoc]
      _ = f12 * e22 * f21 := by rw [he21_e12]
      _ = f12 * f22 * f21 := by rw [he22_f22]
      _ = f12 * f21 := by rw [hf12_f22]
      _ = e := hf12_f21
  have hmul_star : x * star x = e := by
    calc
      x * star x = (e12 * f21) * (f12 * e21) := by rw [hstar_x]
      _ = e12 * (f21 * f12) * e21 := by simp only [mul_assoc]
      _ = e12 * f22 * e21 := by rw [hf21_f12]
      _ = e12 * e22 * e21 := by rw [← he22_f22]
      _ = e12 * e21 := by rw [he12_e22]
      _ = e := he12_e21
  refine ⟨⟨xc, ?_⟩, rfl⟩
  constructor
  · apply Subtype.ext
    exact hstar_mul
  · apply Subtype.ext
    exact hmul_star

/-! ## The matrix retraction -/

/-- Sentence `3c22068a27b2`: if `Ψ ∘ Φ` is an injective corner embedding,
then `Φ` is injective. -/
theorem manuscriptSentence_3c22068a27b2_injectiveOfMatrixRetraction
    {U P M : Type*} [CStarAlgebra U] [CStarAlgebra P] [CStarAlgebra M]
    (Φ : U →⋆ₐ[ℂ] P) (Ψ : P →⋆ₐ[ℂ] M) (δ : U →⋆ₐ[ℂ] M)
    (hcomp : Ψ.comp Φ = δ) (hδ : Function.Injective δ) :
    Function.Injective Φ := by
  intro x y hxy
  apply hδ
  calc
    δ x = Ψ (Φ x) := by
      exact (congrArg (fun f : U →⋆ₐ[ℂ] M ↦ f x) hcomp).symm
    _ = Ψ (Φ y) := congrArg Ψ hxy
    _ = δ y := by
      exact congrArg (fun f : U →⋆ₐ[ℂ] M ↦ f y) hcomp

/-! ## MF heredity -/

/-- The first hereditary assertion in sentence `7b20dd3d1d35`: a corner of
an MF C-star algebra is MF. -/
theorem manuscriptSentence_7b20dd3d1d35_cornerIsMF
    {P : Type u} [CStarAlgebra P]
    (e : P) (he_star : star e = e) (he_mul : e * e = e)
    (hP : IsMFAlgebra P) :
    IsMFAlgebra (CStarCorner e he_star he_mul) :=
  IsMFAlgebra.of_injective_nonUnitalStarAlgHom hP
    (CStarCorner.inclusion e he_star he_mul) Subtype.val_injective

/-- The final hereditary assertion in sentence `7b20dd3d1d35`: an algebra
which embeds faithfully in an MF corner is MF. -/
theorem manuscriptSentence_7b20dd3d1d35_sourceIsMF
    {U : Type u} {P : Type v} [CStarAlgebra U] [CStarAlgebra P]
    (e : P) (he_star : star e = e) (he_mul : e * e = e)
    (hP : IsMFAlgebra P)
    (Φ : U →⋆ₐ[ℂ] CStarCorner e he_star he_mul)
    (hΦ : Function.Injective Φ) :
    IsMFAlgebra U := by
  exact IsMFAlgebra.of_injective_nonUnitalStarAlgHom
    (manuscriptSentence_7b20dd3d1d35_cornerIsMF e he_star he_mul hP)
    Φ.toNonUnitalStarAlgHom hΦ

/-- A closed statement collecting the algebraic and hereditary implications
proved above.  All construction data occur under quantifiers. -/
def PrintedHNNAmalgamCornerPackage : Prop :=
  (∀ (C A B : Type) [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]
      (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
      [Nonempty (CStarAmalgamRepresentation iA iB)]
      (R : CStarAmalgamRepresentation iA iB),
      Function.Injective R.left → Function.Injective R.right →
        Function.Injective (universalCStarAmalgamLeft iA iB) ∧
          Function.Injective (universalCStarAmalgamRight iA iB)) ∧
  (∀ (P : Type) [CStarAlgebra P]
      (e e12 e21 e22 f12 f21 f22 : P)
      (he_star : star e = e) (he_mul : e * e = e)
      (_hstar_e12 : star e12 = e21) (_hstar_f21 : star f21 = f12)
      (_he_e12 : e * e12 = e12) (_hf21_e : f21 * e = f21)
      (_hf21_f12 : f21 * f12 = f22) (_he12_e22 : e12 * e22 = e12)
      (_he12_e21 : e12 * e21 = e) (_he21_e12 : e21 * e12 = e22)
      (_hf12_f22 : f12 * f22 = f12) (_hf12_f21 : f12 * f21 = e)
      (_he22_f22 : e22 = f22),
      ∃ w : unitary (CStarCorner e he_star he_mul),
        ((w : CStarCorner e he_star he_mul) : P) =
          e12 * f21) ∧
  (∀ (U P M : Type) [CStarAlgebra U] [CStarAlgebra P] [CStarAlgebra M]
      (Φ : U →⋆ₐ[ℂ] P) (Ψ : P →⋆ₐ[ℂ] M) (δ : U →⋆ₐ[ℂ] M),
      Ψ.comp Φ = δ → Function.Injective δ → Function.Injective Φ) ∧
  (∀ (U P : Type) [CStarAlgebra U] [CStarAlgebra P]
      (e : P) (he_star : star e = e) (he_mul : e * e = e),
      IsMFAlgebra P →
        ∀ (Φ : U →⋆ₐ[ℂ] CStarCorner e he_star he_mul),
          Function.Injective Φ → IsMFAlgebra U)

theorem printedHNNAmalgamCornerPackage : PrintedHNNAmalgamCornerPackage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C A B _ _ _ iA iB _ R hleft hright
    exact manuscriptSentence_ce5f1d31a90e_factorMapsInjective
      iA iB R hleft hright
  · intro P _ e e12 e21 e22 f12 f21 f22 he_star he_mul
      hstar_e12 hstar_f21 he_e12 hf21_e hf21_f12 he12_e22
      he12_e21 he21_e12 hf12_f22 hf12_f21 he22_f22
    exact manuscriptSentence_6e8a0c1082a2_cornerWordUnitary
      e e12 e21 e22 f12 f21 f22 he_star he_mul hstar_e12 hstar_f21
      he_e12 hf21_e hf21_f12 he12_e22 he12_e21 he21_e12 hf12_f22
      hf12_f21 he22_f22
  · intro U P M _ _ _ Φ Ψ δ hcomp hδ
    exact manuscriptSentence_3c22068a27b2_injectiveOfMatrixRetraction
      Φ Ψ δ hcomp hδ
  · intro U P _ _ e he_star he_mul hP Φ hΦ
    exact manuscriptSentence_7b20dd3d1d35_sourceIsMF
      e he_star he_mul hP Φ hΦ

#audit_axioms manuscriptSentence_ce5f1d31a90e_factorMapsInjective
#audit_axioms manuscriptSentence_68cf3b4da8ab_commonImage
#audit_axioms manuscriptSentence_6e8a0c1082a2_cornerWordUnitary
#audit_axioms manuscriptSentence_3c22068a27b2_injectiveOfMatrixRetraction
#audit_axioms manuscriptSentence_7b20dd3d1d35_cornerIsMF
#audit_axioms manuscriptSentence_7b20dd3d1d35_sourceIsMF
#audit_closed_axioms printedHNNAmalgamCornerPackage

end

end HNNAmalgamCornerSentences
end OneSidedMFRadical
end Manuscript
end GroupApproximation
