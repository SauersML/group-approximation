import GroupApproximation.Sofic.Hyperlinear
import Mathlib.Analysis.Real.Sqrt
import GroupApproximation.Meta.AxiomGuard

/-!
# Sofic and hyperlinear groups as printed (Theorem `thm:main`, tex l.105–109)

`simple_kazhdan_sofic_group.tex`, the paragraph after Theorem `thm:main`:

> (l.105–109) Sofic and hyperlinear groups are defined by approximately multiplicative maps into
> finite symmetric groups with the normalized Hamming distance, and into unitary groups with the
> normalized Hilbert--Schmidt distance, that keep nontrivial elements uniformly far
> from~$1$~\cite{Pestov}.

## Definitions

* `PrintedIsSofic G`: there is `δ > 0` such that for every finite `F ⊆ G` and `ε > 0` there is a map
  `φ : G → Sym(Y)`, `Y` finite and nonempty, with `d_H(φ(gh), φ(g)φ(h)) ≤ ε` for `g, h ∈ F` and
  `δ ≤ d_H(φ(g), 1)` for `1 ≠ g ∈ F`.  `d_H` is the normalized Hamming distance `hammingDistance`.
* `PrintedIsHyperlinear G`: the same with `ψ : G → U(Y)` and the normalized Hilbert–Schmidt distance
  `√(hsDistSq Y A B) = (tr((A - B)*(A - B)) / |Y|)^{1/2}`.

## Agreement with the corpus notions

The corpus notions `GroupApproximation.IsSofic` and `GroupApproximation.IsHyperlinear` (`Sofic.Sofic`,
`Sofic.Hyperlinear`) ask for separation `1 - ε` of distinct elements of `F`.

* `printedIsSofic_of_isSofic`: a corpus sofic model on `F ∪ {1}` at accuracy `min ε (1/4)` has
  `d_H(φ 1, 1) = d_H(φ 1 · φ 1, φ 1) ≤ 1/4`.  The triangle inequality then keeps nontrivial elements
  at distance at least `1/2` from `1`.
* `printedIsHyperlinear_of_printedIsSofic`: `ψ g = permMatrix (φ g)⁻¹` is unitary and doubles the
  squared distance exactly (`permMatrix_hsDistSq`, `hammingDistance_inv`).  Accuracy `ε² / 2` and
  separation `δ` become accuracy `ε` and separation `√(2δ)`.
* `printedIsHyperlinear_of_isSofic`: the composite.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThmMainA

/-- **Sofic groups as printed** (tex l.105–109): approximately multiplicative maps into finite
symmetric groups, in the normalized Hamming distance, keeping nontrivial elements uniformly far
from `1`. -/
def PrintedIsSofic (G : Type*) [Group G] : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteModel) (φ : G → Equiv.Perm Y), 0 < Fintype.card Y ∧
      (∀ g ∈ F, ∀ h ∈ F, hammingDistance Y (φ (g * h)) (φ g * φ h) ≤ ε) ∧
      ∀ g ∈ F, g ≠ 1 → δ ≤ hammingDistance Y (φ g) 1

/-- **Hyperlinear groups as printed** (tex l.105–109): approximately multiplicative maps into
unitary groups, in the normalized Hilbert–Schmidt distance, keeping nontrivial elements uniformly far
from `1`. -/
def PrintedIsHyperlinear (G : Type*) [Group G] : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteModel) (ψ : G → Matrix Y Y ℂ), 0 < Fintype.card Y ∧
      (∀ g, ψ g ∈ Matrix.unitaryGroup Y ℂ) ∧
      (∀ g ∈ F, ∀ h ∈ F, Real.sqrt (hsDistSq Y (ψ (g * h)) (ψ g * ψ h)) ≤ ε) ∧
      ∀ g ∈ F, g ≠ 1 → δ ≤ Real.sqrt (hsDistSq Y (ψ g) 1)

variable {G : Type*} [Group G]

/-- The corpus sofic notion gives the printed one, with uniform separation `1/2` from `1`. -/
theorem printedIsSofic_of_isSofic (hG : IsSofic G) : PrintedIsSofic G := by
  classical
  refine ⟨1 / 2, by norm_num, fun F ε hε => ?_⟩
  obtain ⟨M⟩ := hG (insert 1 F) (min ε (1 / 4)) (lt_min hε (by norm_num))
  have hmin1 : min ε (1 / 4) ≤ ε := min_le_left _ _
  have hmin2 : min ε (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hmul : ∀ g ∈ F, ∀ h ∈ F,
      hammingDistance M.carrier (M.map (g * h)) (M.map g * M.map h) ≤ ε := fun g hg h hh =>
    (M.multiplicative g (Finset.mem_insert_of_mem hg) h (Finset.mem_insert_of_mem hh)).trans hmin1
  have hone : hammingDistance M.carrier 1 (M.map 1) ≤ min ε (1 / 4) := by
    have h1 := M.multiplicative 1 (Finset.mem_insert_self 1 F) 1 (Finset.mem_insert_self 1 F)
    have hinv := hammingDistance_left_invariant M.carrier (M.map 1) 1 (M.map 1)
    rw [mul_one] at h1
    rw [mul_one] at hinv
    rw [hinv] at h1
    exact h1
  refine ⟨M.carrier, M.map, M.nonempty, hmul, fun g hg hg1 => ?_⟩
  have hsep := M.separated g (Finset.mem_insert_of_mem hg) 1 (Finset.mem_insert_self 1 F) hg1
  have htri := hammingDistance_triangle M.carrier (M.map g) 1 (M.map 1)
  linarith

/-- Printed soficity gives printed hyperlinearity through `g ↦ permMatrix (φ g)⁻¹`. -/
theorem printedIsHyperlinear_of_printedIsSofic (hG : PrintedIsSofic G) :
    PrintedIsHyperlinear G := by
  obtain ⟨δ, hδ, hmodels⟩ := hG
  refine ⟨Real.sqrt (2 * δ), Real.sqrt_pos.mpr (mul_pos two_pos hδ), fun F ε hε => ?_⟩
  obtain ⟨Y, φ, hY, hmul, hsep⟩ := hmodels F (ε ^ 2 / 2) (div_pos (pow_pos hε 2) two_pos)
  have hunit : ∀ g, (φ g)⁻¹.permMatrix ℂ ∈ Matrix.unitaryGroup Y ℂ := fun g =>
    permMatrix_mem_unitaryGroup Y _
  have hmul' : ∀ g ∈ F, ∀ h ∈ F,
      Real.sqrt (hsDistSq Y ((φ (g * h))⁻¹.permMatrix ℂ)
        ((φ g)⁻¹.permMatrix ℂ * (φ h)⁻¹.permMatrix ℂ)) ≤ ε := by
    intro g hg h hh
    have hhom : (φ g)⁻¹.permMatrix ℂ * (φ h)⁻¹.permMatrix ℂ = ((φ g * φ h)⁻¹).permMatrix ℂ := by
      rw [_root_.mul_inv_rev, Matrix.permMatrix_mul]
    rw [hhom, permMatrix_hsDistSq, hammingDistance_inv]
    have hle : 2 * hammingDistance Y (φ (g * h)) (φ g * φ h) ≤ ε ^ 2 := by
      have := hmul g hg h hh
      linarith
    calc Real.sqrt (2 * hammingDistance Y (φ (g * h)) (φ g * φ h))
        ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hle
      _ = ε := Real.sqrt_sq hε.le
  have hsep' : ∀ g ∈ F, g ≠ 1 →
      Real.sqrt (2 * δ) ≤ Real.sqrt (hsDistSq Y ((φ g)⁻¹.permMatrix ℂ) 1) := by
    intro g hg hg1
    have hone : (1 : Matrix Y Y ℂ) = (1 : Equiv.Perm Y)⁻¹.permMatrix ℂ := by
      rw [inv_one]
      exact Matrix.permMatrix_one.symm
    rw [hone, permMatrix_hsDistSq, hammingDistance_inv]
    have hle : 2 * δ ≤ 2 * hammingDistance Y (φ g) 1 := by
      have := hsep g hg hg1
      linarith
    exact Real.sqrt_le_sqrt hle
  exact ⟨Y, fun g => (φ g)⁻¹.permMatrix ℂ, hY, hunit, hmul', hsep'⟩

/-- **tex l.105–109, agreement.** A sofic group (corpus notion) is hyperlinear in the printed sense.
-/
theorem printedIsHyperlinear_of_isSofic (hG : IsSofic G) : PrintedIsHyperlinear G :=
  printedIsHyperlinear_of_printedIsSofic (printedIsSofic_of_isSofic hG)

end ThmMainA
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.printedIsSofic_of_isSofic
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.printedIsHyperlinear_of_printedIsSofic
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.printedIsHyperlinear_of_isSofic
