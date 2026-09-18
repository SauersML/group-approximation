import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Spectrum
import GroupApproximation.Analysis.VoiculescuAlmostOrthogonal

/-!
# Quasicentral approximate units, step 1: one averaging step

Lane TWWSch3c2C1, work order WO-TWWSch-3c2-C1.  Manuscript `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378): the absorption argument there uses a
quasicentral approximate unit of the compacts (Arveson 1977, Thm. 1; Kasparov 1980, §3;
Higson--Roe, *Analytic K-homology*, 3.2).

The setting is a non-unital C⋆-algebra `A`, a C⋆-algebra `B` and a `⋆`-homomorphism
`ι : A → B` whose range is a two-sided "ideal" in the weak sense `ι a * y, y * ι a ∈ range ι`
(`hL`, `hR`).  The step is a version of `arvesonPair_exists_average`
(`ChoiEffrosArvesonPairMazur`) along Mathlib's increasing approximate unit
`CStarAlgebra.approximateUnit A`, keeping two extra clauses that the sequence needs:

* the average dominates a given multiple `ρ • a` (`ρ < 1`) of a given positive contraction,
  because every member of the unit eventually does (the basis of the unit is made of the
  sections `{x | ρ • a ≤ x}`), and the average of elements above `ρ • a` is above `ρ • a`;
* it absorbs every member of a finite set `X` from both sides.

Commutators with a finite set `Y ⊆ B` are made small exactly as in the Mazur file: the defects
`[ι e, y]` of a greedy selection are pairwise almost orthogonal
(`quasiUnit_eventually_cross`), so `ShulmanFill.norm_sum_le_of_almostOrthogonal` bounds their
average.  All scalars are real, so positivity is `smul_nonneg`.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter Topology

noncomputable section

/-- The defect identity behind almost orthogonality, for self-adjoint `E`. -/
theorem quasiUnit_defect_mul_star {R : Type*} [NonUnitalRing R] [StarRing R] (D y E : R)
    (hE : IsSelfAdjoint E) :
    D * star (E * y - y * E) = (D * star y * E - D * star y) - (D * E - D) * star y := by
  rw [star_sub, star_mul, star_mul, hE.star_eq]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- The average of `N` vectors of norm at most `d` has norm at most `d`. -/
theorem quasiUnit_norm_avg_le {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (hN : 0 < N) (f : ℕ → E) {d : ℝ} (hf : ∀ i, ‖f i‖ ≤ d) :
    ‖(N : ℝ)⁻¹ • ∑ i ∈ Finset.range N, f i‖ ≤ d := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsum : ‖∑ i ∈ Finset.range N, f i‖ ≤ (N : ℝ) * d := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range N, ‖f i‖ ≤ ∑ _i ∈ Finset.range N, d :=
          Finset.sum_le_sum fun i _ ↦ hf i
      _ = (N : ℝ) * d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hNR.le)]
  calc ((N : ℝ))⁻¹ * ‖∑ i ∈ Finset.range N, f i‖ ≤ ((N : ℝ))⁻¹ * ((N : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hNR.le)
    _ = d := by rw [← mul_assoc, inv_mul_cancel₀ hNR.ne', one_mul]

/-- **Greedy selection along a filter.**  If `P` holds eventually and, for every `a`, so does
`Q a`, then there is a sequence satisfying `P` everywhere and `Q (s i) (s j)` for `i < j < N`. -/
theorem quasiUnit_exists_selection {α : Type*} (l : Filter α) [l.NeBot] (P : α → Prop)
    (Q : α → α → Prop) (hP : ∀ᶠ e in l, P e) (hQ : ∀ a, ∀ᶠ e in l, Q a e) (N : ℕ) :
    ∃ s : ℕ → α, (∀ i, P (s i)) ∧ ∀ i j, i < j → j < N → Q (s i) (s j) := by
  induction N with
  | zero =>
    obtain ⟨e, he⟩ := hP.exists
    exact ⟨fun _ ↦ e, fun _ ↦ he, fun _ j _ hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
    obtain ⟨s, hs, hsQ⟩ := ih
    have hcross : ∀ᶠ e in l, ∀ i ∈ Finset.range N, Q (s i) e := by
      rw [Filter.eventually_all_finset]
      intro i _
      exact hQ (s i)
    obtain ⟨e, he, heQ⟩ := (hP.and hcross).exists
    refine ⟨fun i ↦ if i < N then s i else e, fun i ↦ ?_, ?_⟩
    · by_cases hi : i < N
      · simp only [if_pos hi]
        exact hs i
      · simp only [if_neg hi]
        exact he
    · intro i j hij hj
      by_cases hjN : j < N
      · have hiN : i < N := lt_trans hij hjN
        simp only [if_pos hiN, if_pos hjN]
        exact hsQ i j hij hjN
      · have hiN : i < N := by omega
        simp only [if_pos hiN, if_neg hjN]
        exact heQ i (Finset.mem_range.2 hiN)

section Step

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B]

/-- A `⋆`-homomorphism commutes with real scalars. -/
theorem quasiUnit_map_real_smul (ι : A →⋆ₙₐ[ℂ] B) (r : ℝ) (x : A) : ι (r • x) = r • ι x := by
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul]

/-- A commutator defect `[ι a, y]` lies in the range of `ι`. -/
theorem quasiUnit_defect_mem (ι : A →⋆ₙₐ[ℂ] B) (hL : ∀ (a : A) (y : B), ∃ c : A, ι c = ι a * y)
    (hR : ∀ (a : A) (y : B), ∃ c : A, ι c = y * ι a) (a : A) (y : B) :
    ∃ c : A, ι c = ι a * y - y * ι a := by
  obtain ⟨c₁, hc₁⟩ := hL a y
  obtain ⟨c₂, hc₂⟩ := hR a y
  exact ⟨c₁ - c₂, by rw [map_sub, hc₁, hc₂]⟩

/-- **Cross terms vanish along the unit**: for a fixed `c : A`, eventually
`‖ι c ⋆(ι e y - y ι e)‖ ≤ δ`. -/
theorem quasiUnit_eventually_cross (ι : A →⋆ₙₐ[ℂ] B)
    (hL : ∀ (a : A) (y : B), ∃ c : A, ι c = ι a * y) (c : A) (y : B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ e in CStarAlgebra.approximateUnit A, ‖ι c * star (ι e * y - y * ι e)‖ ≤ δ := by
  obtain ⟨c', hc'⟩ := hL c (star y)
  have hU := CStarAlgebra.increasingApproximateUnit A
  have h1 : Tendsto (fun e ↦ ‖c' * e - c'‖) (CStarAlgebra.approximateUnit A) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hU.tendsto_mul_left c')
  have h2 : Tendsto (fun e ↦ ‖c * e - c‖) (CStarAlgebra.approximateUnit A) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hU.tendsto_mul_left c)
  have hlim : Tendsto (fun e ↦ ‖c' * e - c'‖ + ‖c * e - c‖ * ‖y‖)
      (CStarAlgebra.approximateUnit A) (𝓝 0) := by
    have h := h1.add (h2.mul_const ‖y‖)
    rw [zero_mul, add_zero] at h
    exact h
  filter_upwards [hU.eventually_isSelfAdjoint, hlim.eventually_le_const hδ] with e hesa hsmall
  have hEsa : IsSelfAdjoint (ι e) := hesa.map ι
  have hA : ι c * star y * ι e - ι c * star y = ι (c' * e - c') := by
    rw [map_sub, map_mul, hc']
  have hB : ι c * ι e - ι c = ι (c * e - c) := by
    rw [map_sub, map_mul]
  have hnA : ‖ι (c' * e - c')‖ ≤ ‖c' * e - c'‖ := NonUnitalStarAlgHom.norm_apply_le ι _
  have hnB : ‖ι (c * e - c)‖ ≤ ‖c * e - c‖ := NonUnitalStarAlgHom.norm_apply_le ι _
  have hsm : ‖c' * e - c'‖ + ‖c * e - c‖ * ‖y‖ ≤ δ := hsmall
  rw [quasiUnit_defect_mul_star _ y _ hEsa, hA, hB]
  calc ‖ι (c' * e - c') - ι (c * e - c) * star y‖
      ≤ ‖ι (c' * e - c')‖ + ‖ι (c * e - c) * star y‖ := norm_sub_le _ _
    _ ≤ ‖c' * e - c'‖ + ‖c * e - c‖ * ‖y‖ := by
        refine add_le_add hnA ?_
        calc ‖ι (c * e - c) * star y‖ ≤ ‖ι (c * e - c)‖ * ‖star y‖ := norm_mul_le _ _
          _ ≤ ‖c * e - c‖ * ‖y‖ := by
              rw [norm_star]
              exact mul_le_mul_of_nonneg_right hnB (norm_nonneg y)
    _ ≤ δ := hsm

/-- The properties one selected member of the unit must have. -/
theorem quasiUnit_eventually_good {a : A} (ha : 0 ≤ a) (ha1 : ‖a‖ ≤ 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (X : Finset A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ e in CStarAlgebra.approximateUnit A, 0 ≤ e ∧ ‖e‖ ≤ 1 ∧ ρ • a ≤ e ∧
      ∀ x ∈ X, ‖x - e * x‖ ≤ ε ∧ ‖x - x * e‖ ≤ ε := by
  have hU := CStarAlgebra.increasingApproximateUnit A
  have ha' : 0 ≤ ρ • a := smul_nonneg hρ0 ha
  have ha'1 : ‖ρ • a‖ < 1 := by
    rw [norm_smul, Real.norm_of_nonneg hρ0]
    calc ρ * ‖a‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left ha1 hρ0
      _ < 1 := by linarith
  have hdom : ∀ᶠ e in CStarAlgebra.approximateUnit A, ρ • a ≤ e :=
    (CStarAlgebra.hasBasis_approximateUnit A).eventually_iff.2
      ⟨ρ • a, ⟨ha', ha'1⟩, fun _ hx ↦ hx.1⟩
  refine hU.eventually_nonneg.and (hU.eventually_norm.and (hdom.and ?_))
  rw [Filter.eventually_all_finset]
  intro x _
  have h1 : Tendsto (fun e ↦ ‖e * x - x‖) (CStarAlgebra.approximateUnit A) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hU.tendsto_mul_right x)
  have h2 : Tendsto (fun e ↦ ‖x * e - x‖) (CStarAlgebra.approximateUnit A) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hU.tendsto_mul_left x)
  filter_upwards [h1.eventually_le_const hε, h2.eventually_le_const hε] with e he1 he2
  have he1' : ‖e * x - x‖ ≤ ε := he1
  have he2' : ‖x * e - x‖ ≤ ε := he2
  exact ⟨by rw [norm_sub_rev]; exact he1', by rw [norm_sub_rev]; exact he2'⟩

end Step

end

end TWWSchafhauser
end Full
end GroupApproximation
