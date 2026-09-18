import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDefs

/-!
# Connes' trick, density side: the left-bimodule CPAP gives the full matrix CPAP

Lane TWWSch3b1 (work order WO-TWWSch-3b-1).  This file works toward
`isAmenableTrace_of_isNuclearCStarAlgebra`, the Tikuisis--White--Winter input of
`non_mf_group_notes.tex`.
Source: Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Prop 2.2.6 and
Thm 6.2.7 (the CPAP as used in Connes' trick).

The file was adapted, after review, from the never-wired foreign
`TWWLanes/NuclearDensity/CloseCPAP`, `CloseCPAPStar` and `CloseCPAPReduction` modules.
Here they are restated against this lane's `IsMatrixCPAP` and `IsMatrixLeftBimoduleCPAP`.

`isMatrixCPAP_of_leftBimodule` rebuilds the three clauses that `IsMatrixLeftBimoduleCPAP`
omits.

* The right bimodule clause is the adjoint of the left clause at `a⋆`, because `ρ` and `ψ`
  preserve stars.
* The two multiplicativity clauses follow from the left clause and `ψρ ≈ id`.  These are
  applied on `G = F ∪ F⋆ ∪ F·F ∪ (F·F)⋆` with tolerance `δ / (16 K³)`.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **One bimodule step.**  Suppose `ψ` is left `u`-bimodular up to `δ`, `‖u‖ ≤ K`,
`‖M‖ ≤ L` and `ψ M ≈ c` up to `e`.  Then `ψ(ρ(u) M) ≈ u c` up to `δ L + K e`. -/
theorem norm_bimod_step {A : Type u} [CStarAlgebra A] {Y : FiniteModel}
    (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A) {u : A} {δ K L e : ℝ}
    (hu : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ u * M) - u * ψ M‖ ≤ δ * ‖M‖) (hδ : 0 ≤ δ)
    (huK : ‖u‖ ≤ K) {M : Matrix Y Y ℂ} (hML : ‖M‖ ≤ L) {c : A} (hc : ‖ψ M - c‖ ≤ e) :
    ‖ψ (ρ u * M) - u * c‖ ≤ δ * L + K * e := by
  have e1 : ψ (ρ u * M) - u * c = (ψ (ρ u * M) - u * ψ M) + u * (ψ M - c) := by
    rw [mul_sub]
    abel
  rw [e1]
  calc ‖(ψ (ρ u * M) - u * ψ M) + u * (ψ M - c)‖
      ≤ ‖ψ (ρ u * M) - u * ψ M‖ + ‖u * (ψ M - c)‖ := norm_add_le _ _
    _ ≤ δ * ‖M‖ + ‖u‖ * ‖ψ M - c‖ := add_le_add (hu M) (norm_mul_le _ _)
    _ ≤ δ * L + K * e :=
        add_le_add (mul_le_mul_of_nonneg_left hML hδ)
          (mul_le_mul huK hc (norm_nonneg _) ((norm_nonneg u).trans huK))

/-- **The first multiplicativity estimate.**  Left `a`-bimodularity, `ψρ(b) ≈ b` and
`ψρ(ab) ≈ ab` together bound the defect `ψ(ρ(ab) − ρ(a)ρ(b))` by `δ + (δK + Kδ)`. -/
theorem norm_psi_mul_defect_le {A : Type u} [CStarAlgebra A] {Y : FiniteModel}
    (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A) {a b : A} {δ K : ℝ}
    (hδ : 0 ≤ δ) (ha : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ a * M) - a * ψ M‖ ≤ δ * ‖M‖)
    (haK : ‖a‖ ≤ K) (hRb : ‖ρ b‖ ≤ K) (hb : ‖ψ (ρ b) - b‖ ≤ δ)
    (hab : ‖ψ (ρ (a * b)) - a * b‖ ≤ δ) :
    ‖ψ (ρ (a * b) - ρ a * ρ b)‖ ≤ δ + (δ * K + K * δ) := by
  have step : ‖ψ (ρ a * ρ b) - a * b‖ ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ ha hδ haK hRb hb
  have e1 : ψ (ρ (a * b) - ρ a * ρ b)
      = (ψ (ρ (a * b)) - a * b) - (ψ (ρ a * ρ b) - a * b) := by
    rw [map_sub]
    abel
  rw [e1]
  calc ‖(ψ (ρ (a * b)) - a * b) - (ψ (ρ a * ρ b) - a * b)‖
      ≤ ‖ψ (ρ (a * b)) - a * b‖ + ‖ψ (ρ a * ρ b) - a * b‖ := norm_sub_le _ _
    _ ≤ δ + (δ * K + K * δ) := add_le_add hab step

/-- **The weighted multiplicativity estimate.**  Put `D = ρ(ab) − ρ(a)ρ(b)`.  Assume left
bimodularity at `a`, `a⋆`, `b⋆` and `(ab)⋆`, together with `ψρ(b) ≈ b` and
`ψρ(ab) ≈ ab`.  Then `ψ(D⋆D)` is bounded by an explicit cubic polynomial in `K`.  We expand
`D⋆D` into four terms.  Four chains of `norm_bimod_step` move them close to `(ab)⋆(ab)` or
`b⋆(a⋆(ab))`, and these limits cancel in pairs. -/
theorem norm_psi_star_mul_defect_le {A : Type u} [CStarAlgebra A] {Y : FiniteModel}
    (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (ψ : Matrix Y Y ℂ →ₗ[ℂ] A)
    (hρs : ∀ a : A, ρ (star a) = star (ρ a)) {a b : A} {δ K : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (ha : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ a * M) - a * ψ M‖ ≤ δ * ‖M‖)
    (hsa : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ (star a) * M) - star a * ψ M‖ ≤ δ * ‖M‖)
    (hsb : ∀ M : Matrix Y Y ℂ, ‖ψ (ρ (star b) * M) - star b * ψ M‖ ≤ δ * ‖M‖)
    (hsab : ∀ M : Matrix Y Y ℂ,
      ‖ψ (ρ (star (a * b)) * M) - star (a * b) * ψ M‖ ≤ δ * ‖M‖)
    (haK : ‖a‖ ≤ K) (hsaK : ‖star a‖ ≤ K) (hsbK : ‖star b‖ ≤ K)
    (hsabK : ‖star (a * b)‖ ≤ K) (hRa : ‖ρ a‖ ≤ K) (hRb : ‖ρ b‖ ≤ K)
    (hRab : ‖ρ (a * b)‖ ≤ K) (hRsa : ‖ρ (star a)‖ ≤ K)
    (hb : ‖ψ (ρ b) - b‖ ≤ δ) (hab : ‖ψ (ρ (a * b)) - a * b‖ ≤ δ) :
    ‖ψ (star (ρ (a * b) - ρ a * ρ b) * (ρ (a * b) - ρ a * ρ b))‖
      ≤ (δ * K + K * δ) + (δ * (K * K) + K * (δ * K + K * δ))
        + (δ * (K * K) + K * (δ * K + K * δ))
        + (δ * (K * (K * K)) + K * (δ * (K * K) + K * (δ * K + K * δ))) := by
  have e1 : ‖ψ (ρ a * ρ b) - a * b‖ ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ ha hδ haK hRb hb
  have hRaRb : ‖ρ a * ρ b‖ ≤ K * K :=
    (norm_mul_le _ _).trans (mul_le_mul hRa hRb (norm_nonneg _) hK)
  have hsaP : ‖ρ (star a) * ρ (a * b)‖ ≤ K * K :=
    (norm_mul_le _ _).trans (mul_le_mul hRsa hRab (norm_nonneg _) hK)
  have hsaRR : ‖ρ (star a) * (ρ a * ρ b)‖ ≤ K * (K * K) :=
    (norm_mul_le _ _).trans (mul_le_mul hRsa hRaRb (norm_nonneg _) hK)
  have t1 : ‖ψ (ρ (star (a * b)) * ρ (a * b)) - star (a * b) * (a * b)‖
      ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ hsab hδ hsabK hRab hab
  have t2 : ‖ψ (ρ (star (a * b)) * (ρ a * ρ b)) - star (a * b) * (a * b)‖
      ≤ δ * (K * K) + K * (δ * K + K * δ) :=
    norm_bimod_step ρ ψ hsab hδ hsabK hRaRb e1
  have i3 : ‖ψ (ρ (star a) * ρ (a * b)) - star a * (a * b)‖ ≤ δ * K + K * δ :=
    norm_bimod_step ρ ψ hsa hδ hsaK hRab hab
  have t3 : ‖ψ (ρ (star b) * (ρ (star a) * ρ (a * b))) - star b * (star a * (a * b))‖
      ≤ δ * (K * K) + K * (δ * K + K * δ) :=
    norm_bimod_step ρ ψ hsb hδ hsbK hsaP i3
  have i4 : ‖ψ (ρ (star a) * (ρ a * ρ b)) - star a * (a * b)‖
      ≤ δ * (K * K) + K * (δ * K + K * δ) :=
    norm_bimod_step ρ ψ hsa hδ hsaK hRaRb e1
  have t4 : ‖ψ (ρ (star b) * (ρ (star a) * (ρ a * ρ b))) - star b * (star a * (a * b))‖
      ≤ δ * (K * (K * K)) + K * (δ * (K * K) + K * (δ * K + K * δ)) :=
    norm_bimod_step ρ ψ hsb hδ hsbK hsaRR i4
  have eD : star (ρ (a * b) - ρ a * ρ b) * (ρ (a * b) - ρ a * ρ b)
      = ρ (star (a * b)) * ρ (a * b) - ρ (star (a * b)) * (ρ a * ρ b)
        - ρ (star b) * (ρ (star a) * ρ (a * b))
        + ρ (star b) * (ρ (star a) * (ρ a * ρ b)) := by
    rw [hρs (a * b), hρs b, hρs a, star_sub, star_mul]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  have eψ : ψ (star (ρ (a * b) - ρ a * ρ b) * (ρ (a * b) - ρ a * ρ b))
      = (ψ (ρ (star (a * b)) * ρ (a * b)) - star (a * b) * (a * b))
        - (ψ (ρ (star (a * b)) * (ρ a * ρ b)) - star (a * b) * (a * b))
        - (ψ (ρ (star b) * (ρ (star a) * ρ (a * b))) - star b * (star a * (a * b)))
        + (ψ (ρ (star b) * (ρ (star a) * (ρ a * ρ b))) - star b * (star a * (a * b))) := by
    rw [eD, map_add, map_sub, map_sub]
    abel
  rw [eψ]
  exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)) t4)

/-- **The CPAP reduction.**  The left-bimodule matrix CPAP implies the full
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

end

end GroupApproximation.Full.TWWSchafhauser.Connes
