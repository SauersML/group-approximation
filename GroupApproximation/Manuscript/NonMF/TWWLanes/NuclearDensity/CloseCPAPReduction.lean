import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.CloseCPAPStar
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-25, part 3: `IsMatrixLeftBimoduleCPAP A → IsMatrixCPAP A`

Take `F` and `δ > 0`.  Let `G = F ∪ F⋆ ∪ F·F ∪ (F·F)⋆`, choose `K ≥ 1` bounding the norms
on `G`, and apply the smaller Statement at `G` with tolerance `δ' = δ / (16 K³)`.

* `ψρ ≈ id` and the left clause on `F` pass from `δ'` to `δ`.
* **Right clause.**  This is the adjoint of the left clause at `a⋆` and `M⋆`:
  `ψ(ρ(a⋆)M⋆) − a⋆ψ(M⋆) = (ψ(Mρ(a)) − ψ(M)a)⋆`, and `‖M⋆‖ = ‖M‖`.
* **Multiplicativity clauses.**  Use `norm_psi_mul_defect_le` and
  `norm_psi_star_mul_defect_le`.  Each bound is a sum of terms `c·Kʲ·δ'` with `j ≤ 3`,
  and the total at most `16 K³ δ' = δ`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- **The `cpap` reduction.**  The left-bimodule matrix CPAP implies the full
`IsMatrixCPAP`, clause by clause. -/
theorem isMatrixCPAP_of_leftBimodule {A : Type u} [CStarAlgebra A]
    (h : IsMatrixLeftBimoduleCPAP A) : IsMatrixCPAP A := by
  classical
  intro F δ hδ
  obtain ⟨G, hGF, hGs, hGm, hGms⟩ : ∃ G : Finset A, (∀ a ∈ F, a ∈ G) ∧
      (∀ a ∈ F, star a ∈ G) ∧ (∀ a ∈ F, ∀ b ∈ F, a * b ∈ G) ∧
      (∀ a ∈ F, ∀ b ∈ F, star (a * b) ∈ G) := by
    refine ⟨F ∪ F.image star ∪ (F ×ˢ F).image (fun p : A × A ↦ p.1 * p.2)
      ∪ (F ×ˢ F).image (fun p : A × A ↦ star (p.1 * p.2)), ?_, ?_, ?_, ?_⟩
    · intro a ha
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
    · intro a ha
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image_of_mem star ha)))
    · intro a ha b hb
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun p : A × A ↦ p.1 * p.2)
          (Finset.mem_product.mpr ⟨ha, hb⟩ : (a, b) ∈ F ×ˢ F)))
    · intro a ha b hb
      exact Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun p : A × A ↦ star (p.1 * p.2))
          (Finset.mem_product.mpr ⟨ha, hb⟩ : (a, b) ∈ F ×ˢ F))
  obtain ⟨K, hK1, hKG⟩ : ∃ K : ℝ, 1 ≤ K ∧ ∀ z ∈ G, ‖z‖ ≤ K := by
    refine ⟨1 + ∑ x ∈ G, ‖x‖, ?_, fun z hz ↦ ?_⟩
    · have hs : 0 ≤ ∑ x ∈ G, ‖x‖ := Finset.sum_nonneg fun x _ ↦ norm_nonneg x
      linarith
    · have hs : ‖z‖ ≤ ∑ x ∈ G, ‖x‖ := Finset.single_le_sum (fun x _ ↦ norm_nonneg x) hz
      linarith
  have hK0 : 0 < K := by linarith
  have hk3 : 1 ≤ K * (K * K) :=
    one_le_mul_of_one_le_of_one_le hK1 (one_le_mul_of_one_le_of_one_le hK1 hK1)
  have hden : 0 < 16 * (K * (K * K)) := by linarith
  obtain ⟨δ', hδ', hδ'eq⟩ : ∃ δ' : ℝ, 0 < δ' ∧ 16 * (K * (K * K)) * δ' = δ :=
    ⟨δ / (16 * (K * (K * K))), div_pos hδ hden, mul_div_cancel₀ δ hden.ne'⟩
  have hA1 : δ' ≤ K * δ' := le_mul_of_one_le_left hδ'.le hK1
  have hA2 : K * δ' ≤ K * (K * δ') := le_mul_of_one_le_left (mul_pos hK0 hδ').le hK1
  have hA3 : K * (K * δ') ≤ K * (K * (K * δ')) :=
    le_mul_of_one_le_left (mul_pos hK0 (mul_pos hK0 hδ')).le hK1
  have hδ'le : δ' ≤ δ := by linarith
  obtain ⟨Y, ρ, ψ, hρ1, hρcp, hρn, hρs, hψ1, hψpos, hψs, hψρ, hbim⟩ := h G δ' hδ'
  have hRK : ∀ z ∈ G, ‖ρ z‖ ≤ K := fun z hz ↦ (hρn z).trans (hKG z hz)
  refine ⟨Y, ρ, ψ, hρ1, hρcp, hρn, hρs, hψ1, hψpos, hψs, fun a ha ↦ ?_,
    fun a ha M ↦ ⟨?_, ?_⟩, fun a ha b hb ↦ ?_, fun a ha b hb ↦ ?_⟩
  · exact (hψρ a (hGF a ha)).trans hδ'le
  · exact (hbim a (hGF a ha) M).trans (mul_le_mul_of_nonneg_right hδ'le (norm_nonneg M))
  · have hsN : ‖star M‖ = ‖M‖ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    have e1 : ψ (ρ (star a) * star M) - star a * ψ (star M)
        = star (ψ (M * ρ a) - ψ M * a) := by
      rw [hρs, ← star_mul, hψs, hψs, ← star_mul, ← star_sub]
    calc ‖ψ (M * ρ a) - ψ M * a‖ = ‖star (ψ (M * ρ a) - ψ M * a)‖ := (norm_star _).symm
      _ = ‖ψ (ρ (star a) * star M) - star a * ψ (star M)‖ := by rw [e1]
      _ ≤ δ' * ‖star M‖ := hbim (star a) (hGs a ha) (star M)
      _ ≤ δ * ‖M‖ := by
          rw [hsN]
          exact mul_le_mul_of_nonneg_right hδ'le (norm_nonneg M)
  · refine (norm_psi_mul_defect_le ρ ψ hδ'.le (hbim a (hGF a ha)) (hKG a (hGF a ha))
      (hRK b (hGF b hb)) (hψρ b (hGF b hb)) (hψρ (a * b) (hGm a ha b hb))).trans ?_
    linarith
  · refine (norm_psi_star_mul_defect_le ρ ψ hρs hδ'.le hK0.le (hbim a (hGF a ha))
      (hbim (star a) (hGs a ha)) (hbim (star b) (hGs b hb))
      (hbim (star (a * b)) (hGms a ha b hb)) (hKG a (hGF a ha)) (hKG (star a) (hGs a ha))
      (hKG (star b) (hGs b hb)) (hKG (star (a * b)) (hGms a ha b hb)) (hRK a (hGF a ha))
      (hRK b (hGF b hb)) (hRK (a * b) (hGm a ha b hb)) (hRK (star a) (hGs a ha))
      (hψρ b (hGF b hb)) (hψρ (a * b) (hGm a ha b hb))).trans ?_
    linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.isMatrixCPAP_of_leftBimodule

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
