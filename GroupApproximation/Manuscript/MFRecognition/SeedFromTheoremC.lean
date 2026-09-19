import GroupApproximation.Manuscript.NonMF.TheoremCAssembly
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Sofic.CDEOperatorMF

/-!
# `lem:seed`: the seed is the group of Theorem C

> **Lemma (`lem:seed`).**  There is a fixed finite presentation `P₋` whose
> group `E = G_{P₋}` is not MF.
>
> *Proof.*  Theorem C of `[NonMF]` gives a finitely presented torsion-free
> group that equals its own MF radical, and a nontrivial group equal to its own
> MF radical is not MF.  Fix one finite presentation code `P₋` for this group.

This module follows the printed proof literally.  `E` is the group of
Theorem C (`TheoremC.manuscriptTorsionFreeFullMFRadical_closed`, closed on
the explicit inputs of `TheoremCAssembly`); it is nontrivial because it is
acylindrically hyperbolic; it is not MF because its MF radical is everything;
and `seedCodeC` is one finite presentation code for it, chosen by the adequacy
of the coding (`exists_code_mulEquiv`).
-/

namespace GroupApproximation

/-! ## A loxodromic element is not the identity -/

namespace HullGeometry

variable {G X : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X]

/-- A loxodromic element is not the identity: the identity moves nothing,
while a loxodromic element moves the basepoint linearly far. -/
theorem IsLoxodromic.ne_one {g : G} {x : X} (h : IsLoxodromic g x) : g ≠ 1 := by
  rintro rfl
  obtain ⟨l, hl, B, _, hlin⟩ := h
  obtain ⟨n, hn⟩ := exists_nat_gt (B / l)
  have hdist := hlin n
  rw [one_pow, one_smul, dist_self] at hdist
  have : B < l * n := by
    rw [div_lt_iff₀ hl, mul_comm] at hn
    exact hn
  linarith

end HullGeometry

namespace Manuscript
namespace NonMF
namespace TorsionFree

/-- An acylindrically hyperbolic group is nontrivial: it contains a loxodromic
element. -/
theorem nontrivial_of_isAcylindricallyHyperbolic (G : Type) [Group G]
    [IsAcylindricallyHyperbolic G] : Nontrivial G := by
  obtain ⟨A, δ, _, _, g, _, _, _, hg, _, _⟩ := (‹IsAcylindricallyHyperbolic G›).out
  exact ⟨⟨g, 1, HullGeometry.IsLoxodromic.ne_one hg⟩⟩

end TorsionFree
end NonMF

namespace MFRecognition
namespace SeedFromTheoremC

open NonMF.TheoremC
open PresentationCodes

noncomputable section

/-- **The paper's `E`**: the group of Theorem C. -/
def E : Type := manuscriptTorsionFreeFullMFRadical_closed.choose

instance instGroupE : Group E := manuscriptTorsionFreeFullMFRadical_closed.choose_spec.choose

/-- The printed clauses of Theorem C, at `E`. -/
theorem E_spec :
    IsTwoGenerated E ∧ Group.IsFinitelyPresented E ∧ IsPowerTorsionFree E ∧
      NonMF.TorsionFree.IsAcylindricallyHyperbolic E ∧ HasKazhdanPropertyT.{0, 0} E ∧
      manuscriptCoronaMFResidual E = ⊤ ∧
      (∀ (L : Type) (_ : Group L) (r : E →* L), Function.Surjective r →
        Nontrivial L → manuscriptCoronaMFResidual L = ⊤) ∧
      (∀ (L : Type) (_ : Group L) (r : E →* L),
        Function.Surjective r → Nontrivial L → ¬ IsOperatorMF L) :=
  manuscriptTorsionFreeFullMFRadical_closed.choose_spec.choose_spec

instance instFinitelyPresentedE : Group.IsFinitelyPresented E := E_spec.2.1

instance instAcylindricallyHyperbolicE : NonMF.TorsionFree.IsAcylindricallyHyperbolic E :=
  E_spec.2.2.2.1

instance instCountableE : Countable E := ChiodoBelegradek.countable_of_isFinitelyPresented E

instance instNontrivialE : Nontrivial E :=
  NonMF.TorsionFree.nontrivial_of_isAcylindricallyHyperbolic E

/-- "a nontrivial group equal to its own MF radical is not MF": `E` is not MF. -/
theorem E_not_isOperatorMF : ¬ IsOperatorMF E := by
  intro h
  exact E_spec.2.2.2.2.2.2.2 E inferInstance (MonoidHom.id E)
    Function.surjective_id inferInstance h

/-- **"Fix one finite presentation code `P₋` for this group."** -/
def seedCodeC : PresentationCode := (exists_code_mulEquiv E).choose

/-- The code presents `E`. -/
def seedCodeC_equiv : Carrier seedCodeC ≃* E := (exists_code_mulEquiv E).choose_spec.some

/-- **`lem:seed`**: the seed presentation's group is not MF. -/
theorem not_isOperatorMF_seedCodeC : ¬ IsOperatorMF (Carrier seedCodeC) := by
  intro h
  exact E_not_isOperatorMF
    (h.comap seedCodeC_equiv.symm.toMonoidHom seedCodeC_equiv.symm.injective)

end

end SeedFromTheoremC
end MFRecognition
end Manuscript
end GroupApproximation
