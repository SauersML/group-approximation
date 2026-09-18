import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.Definition
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# The Elek–Szabó normalization gives corpus hyperlinearity, tex 345–348

`simple_kazhdan_sofic_group.tex`, l.345–348:

> It is LEF, so it is sofic~\cite[Example~4.5]{Pestov} and
> hyperlinear~\cite[Theorem~2]{ElekSzabo}, ...

`isHyperlinear_of_isHyperlinearElekSzabo : IsHyperlinearElekSzabo G → IsHyperlinear G`.

Proof route.  Given `F` and `ε`, put `η = min (ε/5) 1` and take an Elek–Szabó map `φ` on
`T = F ∪ {h⁻¹ g | g, h ∈ F}` at accuracy `η`; the corpus model is `φ` on `esModel n`.

* Multiplicativity: `‖φ(gh) − φ(g)φ(h)‖₂ < η` gives `hsDistSq ≤ η² ≤ ε` (`Real.sqrt_lt'`).
* Separation (`sep_hsDistSq_ge`).  For `g ≠ h` in `F` put `k = h⁻¹ g ∈ T`, `k ≠ 1`, so
  `‖φ g − φ h φ k‖₂ < η` and `‖φ k − 1‖₂ ≥ √2 − η`.  With `τ(φ h φ k φ h*) = τ(φ k)` and
  Cauchy–Schwarz (`normSq_normTrace_le_hsNormSq`, `hsNormSq_mul_right`),
  `Re τ(φ g φ h*) ≤ Re τ(φ k) + η`, hence
  `hsDistSq(φ g, φ h) = 2 − 2 Re τ(φ g φ h*) ≥ ‖φ k − 1‖₂² − 2η ≥ (√2 − η)² − 2η ≥ 2 − 5η`,
  using `√2 < 3/2`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SkRows
namespace HyperlinearElekSzabo

open Matrix

/-- If `A ≈ B K` within `η` and `‖K − 1‖₂² ≥ c`, then `A` and `B` are `c − 2η` apart in squared
normalized Hilbert–Schmidt distance (all three unitary). -/
theorem sep_hsDistSq_ge (Y : FiniteModel) (hY : 0 < Fintype.card Y) {A B K : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (hK : K ∈ Matrix.unitaryGroup Y ℂ) {η c : ℝ} (hη : 0 ≤ η)
    (hm : hsNormSq Y (A - B * K) ≤ η ^ 2) (hs : c ≤ hsNormSq Y (K - 1)) :
    c - 2 * η ≤ hsDistSq Y A B := by
  have hBB : Bᴴ * B = 1 := by
    have h := hB
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hBc : Bᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    have h := hB
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have htrK : normTrace Y (B * K * Bᴴ) = normTrace Y K := by
    have htr : Matrix.trace (B * K * Bᴴ) = Matrix.trace K := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB, Matrix.one_mul]
    rw [normTrace, normTrace, htr]
  have hK1 : hsNormSq Y (K - 1) = 2 - 2 * (normTrace Y K).re := by
    have h := hsDistSq_of_unitary Y (B := 1) hK (Submonoid.one_mem _) hY
    rw [Matrix.conjTranspose_one, Matrix.mul_one] at h
    exact h
  have hAB := hsDistSq_of_unitary Y hA hB hY
  have hdiff : Complex.normSq (normTrace Y (A * Bᴴ) - normTrace Y K) ≤ η ^ 2 := by
    rw [← htrK, ← normTrace_sub, ← Matrix.sub_mul]
    calc Complex.normSq (normTrace Y ((A - B * K) * Bᴴ))
        ≤ hsNormSq Y ((A - B * K) * Bᴴ) := normSq_normTrace_le_hsNormSq _ _
      _ = hsNormSq Y (A - B * K) := hsNormSq_mul_right Y hBc _
      _ ≤ η ^ 2 := hm
  have hre : (normTrace Y (A * Bᴴ)).re - (normTrace Y K).re ≤ η := by
    have hsq : (normTrace Y (A * Bᴴ) - normTrace Y K).re ^ 2 ≤ η ^ 2 := by
      rw [Complex.normSq_apply] at hdiff
      nlinarith [mul_self_nonneg (normTrace Y (A * Bᴴ) - normTrace Y K).im]
    have hle := (abs_le_of_sq_le_sq' hsq hη).2
    rw [Complex.sub_re] at hle
    exact hle
  rw [hK1] at hs
  rw [hAB]
  linarith

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.sep_hsDistSq_ge

/-- Hyperlinearity in the printed Elek–Szabó normalization implies corpus hyperlinearity. -/
theorem isHyperlinear_of_isHyperlinearElekSzabo {G : Type*} [Group G]
    (hES : IsHyperlinearElekSzabo G) : IsHyperlinear G := by
  classical
  intro F ε hε
  obtain ⟨η, hη0, hη5, hη1⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ ε / 5 ∧ η ≤ 1 :=
    ⟨min (ε / 5) 1, lt_min (div_pos hε (by norm_num)) one_pos, min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨n, φ, hn, hU, hmul, hsep⟩ :=
    hES (F ∪ (F ×ˢ F).image (fun p : G × G ↦ p.1⁻¹ * p.2)) η hη0
  have hcard : 0 < Fintype.card (esModel n) := lt_of_lt_of_eq hn (card_esModel n).symm
  refine ⟨{ carrier := esModel n, nonempty := hcard, map := φ, isUnitary := hU,
    multiplicative := ?_, separated := ?_ }⟩
  · intro g hg k hk
    have hm := hmul g (Finset.mem_union_left _ hg) k (Finset.mem_union_left _ hk)
    rw [esNorm_eq, Real.sqrt_lt' hη0] at hm
    exact le_trans hm.le (by nlinarith [mul_nonneg hη0.le (sub_nonneg.2 hη1)])
  · intro g hg k hk hgk
    have hmem : k⁻¹ * g ∈ F ∪ (F ×ˢ F).image (fun p : G × G ↦ p.1⁻¹ * p.2) :=
      Finset.mem_union_right _
        (Finset.mem_image.2 ⟨(k, g), Finset.mk_mem_product hk hg, rfl⟩)
    have hk1 : k⁻¹ * g ≠ 1 := fun hc ↦ hgk (inv_mul_eq_one.1 hc).symm
    have hm := hmul k (Finset.mem_union_left _ hk) (k⁻¹ * g) hmem
    rw [mul_inv_cancel_left, esNorm_eq] at hm
    have hm2 := ((Real.sqrt_lt' hη0).1 hm).le
    have hs := hsep (k⁻¹ * g) hmem hk1
    rw [esNorm_eq] at hs
    have hpos : 0 < Real.sqrt 2 - η := by linarith [Real.one_lt_sqrt_two]
    have hs2 := (Real.le_sqrt' hpos).1 hs
    have hX := sep_hsDistSq_ge (esModel n) hcard (hU g) (hU k) (hU (k⁻¹ * g)) hη0.le hm2 hs2
    have hsqrt : Real.sqrt 2 < 3 / 2 := Real.sqrt_two_lt_three_halves
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hq : 2 - ε ≤ (Real.sqrt 2 - η) ^ 2 - 2 * η := by
      nlinarith [mul_le_mul_of_nonneg_right hsqrt.le hη0.le, sq_nonneg η]
    exact le_trans hq hX

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.HyperlinearElekSzabo.isHyperlinear_of_isHyperlinearElekSzabo

end HyperlinearElekSzabo
end SkRows
end SimpleKazhdanSofic
end GroupApproximation
