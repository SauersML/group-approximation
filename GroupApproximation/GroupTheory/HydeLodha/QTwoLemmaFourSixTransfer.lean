import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixStatements
import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationProduct
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Lemma 4.6: the casing pair and conjugation into the unit frame

Hyde–Lodha, proof of Lemma 4.6: "We will prove the lemma by isolating a group `H ≅ F_{η_n}` such that
`⟨f, H⟩, Υ_{Γ_n}(I)` is a casing pair for `Υ_Γ(I)`, which will imply that `Υ_Γ(I)` is of type `F_∞`
using Lemma 4.2."

In the unit frame `0 < a < b < 1`, `LemmaFourSixCaseOneStatement` gives a finitely presented
`N ≤ Υ_{Q₂}(I)` containing `Υ_{Γ₂}(I)'`.  For `Q₂ ≤ Γ ≤ Γ₂` this is the chain
`Υ_{Γ₂}(I)' ≤ N ≤ Υ_Γ(I) ≤ Υ_{Γ₂}(I)`.  `Υ_{Γ₂}(I)` is finitely presented by Lemma 4.5, so Lemma 4.2
(`isFinitelyPresented_of_commutator_le`) makes `Υ_Γ(I)` finitely presented.  A general grid interval
with `|I| < 1` is moved into the unit frame by an element of `Γ₂` and an integer translation.

* `isFinitelyPresented_upsilon_unit_of_caseOne`: the casing pair in the unit frame.
* `isFinitelyPresented_upsilon_short_of_caseOne`: conjugation into the unit frame.
* `UpsilonShortOfCaseOne`, `upsilonShortOfCaseOne`: every grid interval with `a < b < a + 1`, from Case 1.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-- **Hyde–Lodha, proof of Lemma 4.6**, the casing pair in the unit frame:
`Υ_{Γ₂}(I)' ≤ N ≤ Υ_Γ(I) ≤ Υ_{Γ₂}(I)`. -/
theorem isFinitelyPresented_upsilon_unit_of_caseOne (h1 : LemmaFourSixCaseOneStatement)
    {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) {a b : ℚ}
    (ha : ∃ M, a ∈ Grid 6 M) (hb : ∃ M, b ∈ Grid 6 M) (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    Group.IsFinitelyPresented ↥(upsilon Γ a b) := by
  obtain ⟨N, hNfp, hNQ, hKN⟩ := h1 a b ha hb h0a hab hb1
  haveI := hNfp
  haveI := isFinitelyPresented_upsilon_gammaTwo_unit ha hb h0a hab hb1
  haveI : Group.FG ↥(upsilon gammaTwo a b) := ProductFinitePresentation.fg_of_isFinitelyPresented _
  exact isFinitelyPresented_of_commutator_le N (upsilon Γ a b) (upsilon gammaTwo a b)
    (hNQ.trans (upsilon_mono hQ subset_rfl)) (upsilon_mono hΓ subset_rfl) hKN

/-- **Hyde–Lodha, proof of Lemma 4.6**, `|I| < 1`: conjugation into the unit frame. -/
theorem isFinitelyPresented_upsilon_short_of_caseOne (h1 : LemmaFourSixCaseOneStatement)
    {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) {a b : ℚ}
    (ha : ∃ M, a ∈ Grid 6 M) (hb : ∃ M, b ∈ Grid 6 M) (hab : a < b) (hba : b - a < 1) :
    Group.IsFinitelyPresented ↥(upsilon Γ a b) := by
  obtain ⟨g, hg, j, hj0, hj1⟩ := exists_move_into_unit ha hb hab hba
  have hgmono := gammaTwo_strictMono hg
  obtain ⟨Ma, hMa⟩ := gammaTwo_apply_grid hg ha
  obtain ⟨Mb, hMb⟩ := gammaTwo_apply_grid hg hb
  have hgaG : ∃ M, g a + j ∈ Grid 6 M := ⟨Ma, grid_add hMa (int_mem_grid Ma j)⟩
  have hgbG : ∃ M, g b + j ∈ Grid 6 M := ⟨Mb, grid_add hMb (int_mem_grid Mb j)⟩
  haveI := isFinitelyPresented_upsilon_unit_of_caseOne h1 hQ hΓ hgaG hgbG hj0
    (by have := hgmono hab; linarith) hj1
  have e : upsilon Γ (g a + j) (g b + j) = upsilon Γ (g a) (g b) := upsilon_add_int Γ (g a) (g b) j
  haveI : Group.IsFinitelyPresented ↥(upsilon Γ (g a) (g b)) :=
    Group.IsFinitelyPresented.equiv (MulEquiv.subgroupCongr e)
  exact Group.IsFinitelyPresented.equiv (upsilonConjEquiv hQ hΓ hg a b).symm

/-- **Hyde–Lodha, proof of Lemma 4.6, `|I| < 1`**: Case 1 in the unit frame makes `Υ_Γ([a, b])` finitely
presented for every `Q₂ ≤ Γ ≤ Γ₂` and every grid interval with `a < b < a + 1`. -/
def UpsilonShortOfCaseOne : Prop :=
  LemmaFourSixCaseOneStatement →
    ∀ Γ : Subgroup (Equiv.Perm ℚ), qTwo ≤ Γ → Γ ≤ gammaTwo → ∀ a b : ℚ, (∃ M, a ∈ Grid 6 M) →
      (∃ M, b ∈ Grid 6 M) → a < b → b < a + 1 → Group.IsFinitelyPresented ↥(upsilon Γ a b)

theorem upsilonShortOfCaseOne : UpsilonShortOfCaseOne := by
  intro h1 Γ hQ hΓ a b ha hb hab hba
  exact isFinitelyPresented_upsilon_short_of_caseOne h1 hQ hΓ ha hb hab (by linarith)

#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_unit_of_caseOne
#audit_axioms GroupApproximation.HydeLodha.isFinitelyPresented_upsilon_short_of_caseOne
#audit_axioms GroupApproximation.HydeLodha.upsilonShortOfCaseOne

end HydeLodha
end GroupApproximation
