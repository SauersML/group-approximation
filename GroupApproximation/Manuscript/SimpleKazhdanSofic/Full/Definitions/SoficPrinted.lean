import GroupApproximation.Sofic.SoficAmplification
import GroupApproximation.Sofic.Hyperlinear
import Mathlib.Analysis.Real.Sqrt
import GroupApproximation.Meta.AxiomGuard

/-!
# Sofic and hyperlinear groups as printed (`thm:main`, tex l.105–109)

`simple_kazhdan_sofic_group.tex`, the paragraph after Theorem `thm:main` (gap report, Lane 1, item
D1):

> Sofic and hyperlinear groups are defined by approximately multiplicative maps into finite
> symmetric groups with the normalized Hamming distance, and into unitary groups with the
> normalized Hilbert--Schmidt distance, that keep nontrivial elements uniformly far from~$1$.

## Definitions

* `PrintedIsSofic G`: there is `δ > 0` such that for every finite `F ⊆ G` and `ε > 0` there is a map
  `φ : G → Sym(Y)`, `Y` finite and nonempty, with `d_H(φ(gh), φ(g)φ(h)) ≤ ε` for `g, h ∈ F` and
  `δ ≤ d_H(φ(g), 1)` for `1 ≠ g ∈ F`.
* `PrintedIsHyperlinear G`: the same with unitary `ψ : G → U(Y)` and the normalized
  Hilbert–Schmidt distance `√(hsDistSq Y A B)`.

## Agreement with the corpus notions

The corpus notions `IsSofic` and `IsHyperlinear` ask for separation `1 - ε` (resp. `2 - ε`) between
distinct elements of `F`.

* `printedIsSofic_of_isSofic`: a corpus model on `F ∪ {1}` at accuracy `min ε (1/4)` has
  `d_H(φ 1, 1) ≤ 1/4`, so nontrivial elements stay at distance `1/2` from `1`.
* `isSofic_of_printedIsSofic`: a printed model on `F ∪ F⁻¹ ∪ F⁻¹F ∪ {1}` at accuracy
  `min ε (δ/8)` separates distinct `g, h ∈ F` by `δ/2`, through `φ(h)⁻¹`-invariance and
  `h⁻¹ g ≠ 1`.  `isSofic_of_isSoficWeak` amplifies the separation.
* `printedIsSofic_iff`.
* `printedIsHyperlinear_of_printedIsSofic`, `printedIsHyperlinear_of_isSofic`: permutation matrices
  `permMatrix (φ g)⁻¹` double squared distances.
-/

namespace GroupApproximation.Full.SK01

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

/-- The printed sofic notion gives the corpus one: printed models on `F ∪ F⁻¹ ∪ F⁻¹F ∪ {1}`
separate distinct elements of `F` by `δ / 2`, and `isSofic_of_isSoficWeak` amplifies. -/
theorem isSofic_of_printedIsSofic (hG : PrintedIsSofic G) : IsSofic G := by
  classical
  obtain ⟨δ, hδ, hmodels⟩ := hG
  refine isSofic_of_isSoficWeak (half_pos hδ) ?_
  intro F ε hε
  have hF' : ∃ F' : Finset G, (1 : G) ∈ F' ∧ (∀ g ∈ F, g ∈ F') ∧ (∀ h ∈ F, h⁻¹ ∈ F') ∧
      ∀ g ∈ F, ∀ h ∈ F, h⁻¹ * g ∈ F' :=
    ⟨insert 1 (F ∪ F.image (fun a : G => a⁻¹) ∪ Finset.image₂ (fun a b : G => a⁻¹ * b) F F),
      Finset.mem_insert_self _ _,
      fun g hg => Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hg)),
      fun h hh => Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun a : G => a⁻¹) hh))),
      fun g hg h hh => Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image₂_of_mem (f := fun a b : G => a⁻¹ * b) hh hg))⟩
  obtain ⟨F', h1F, hFF, hinvF, hdivF⟩ := hF'
  have hη : 0 < min ε (δ / 8) := lt_min hε (div_pos hδ (by norm_num))
  have hη1 : min ε (δ / 8) ≤ ε := min_le_left _ _
  have hη2 : min ε (δ / 8) ≤ δ / 8 := min_le_right _ _
  obtain ⟨Y, φ, hY, hmul, hsep⟩ := hmodels F' (min ε (δ / 8)) hη
  have hmulW : ∀ g ∈ F, ∀ h ∈ F, hammingDistance Y (φ (g * h)) (φ g * φ h) ≤ ε :=
    fun g hg h hh => (hmul g (hFF g hg) h (hFF h hh)).trans hη1
  -- `φ 1` is close to `1`.
  have hone : hammingDistance Y (φ 1) 1 ≤ min ε (δ / 8) := by
    have m3 := hmul 1 h1F 1 h1F
    rw [mul_one] at m3
    have e1 := hammingDistance_left_invariant Y (φ 1) (φ 1) 1
    rw [mul_one] at e1
    have c1 := hammingDistance_comm Y (φ 1) (φ 1 * φ 1)
    linarith
  have hsepW : ∀ g ∈ F, ∀ h ∈ F, g ≠ h → δ / 2 ≤ hammingDistance Y (φ g) (φ h) := by
    intro g hg h hh hne
    have hne' : h⁻¹ * g ≠ 1 := fun heq => hne (inv_mul_eq_one.mp heq).symm
    have s1 := hsep (h⁻¹ * g) (hdivF g hg h hh) hne'
    have m1 := hmul h⁻¹ (hinvF h hh) g (hFF g hg)
    have m2 := hmul h⁻¹ (hinvF h hh) h (hFF h hh)
    rw [inv_mul_cancel] at m2
    have t1 := hammingDistance_triangle Y (φ (h⁻¹ * g)) (φ h⁻¹ * φ g) 1
    have t2 := hammingDistance_triangle Y (φ h⁻¹ * φ g) (φ h⁻¹ * φ h) 1
    have t3 := hammingDistance_triangle Y (φ h⁻¹ * φ h) (φ 1) 1
    have c2 := hammingDistance_comm Y (φ 1) (φ h⁻¹ * φ h)
    have e2 := hammingDistance_left_invariant Y (φ h⁻¹) (φ g) (φ h)
    linarith
  exact ⟨{ carrier := Y, nonempty := hY, map := φ, multiplicative := hmulW,
    separated := hsepW }⟩

/-- **tex l.105–109, sofic.** The printed definition of sofic groups is the corpus notion. -/
theorem printedIsSofic_iff : PrintedIsSofic G ↔ IsSofic G :=
  ⟨isSofic_of_printedIsSofic, printedIsSofic_of_isSofic⟩

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

/-- **tex l.105–109, agreement.** A sofic group is hyperlinear in the printed sense. -/
theorem printedIsHyperlinear_of_isSofic (hG : IsSofic G) : PrintedIsHyperlinear G :=
  printedIsHyperlinear_of_printedIsSofic (printedIsSofic_of_isSofic hG)

end GroupApproximation.Full.SK01

#audit_axioms GroupApproximation.Full.SK01.printedIsSofic_iff
#audit_axioms GroupApproximation.Full.SK01.printedIsHyperlinear_of_isSofic
