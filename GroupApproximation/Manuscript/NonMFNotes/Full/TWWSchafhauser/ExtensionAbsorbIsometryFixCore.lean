import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbDominant
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# The polar correction of a near isometry

Lane `TWWSch3c2-C3b`, work order `WO-TWWSch-3c2-C3b`. Sources: G. A. Elliott and D. Kucerovsky,
Pacific J. Math. 198 (2001), proof of Thm. 6; G. J. Murphy, *C⋆-algebras and operator theory*,
Thm. 2.1.13 (continuous functional calculus). Manuscript label: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (the absorption step).

Let `w` be a near isometry of `H_J` (`IsStdNearIsometry`): `k = w⋆w − 1` is compact and
`‖k‖ ≤ c < 1`. Then `w' = w (w⋆w)^{-1/2}` is an isometry, and `w' − w = w ((1+k)^{-1/2} − 1)` is
compact because `(1+k)^{-1/2} − 1 = k · h(k)` for a continuous `h`.

The analytic part is done here in an arbitrary unital C⋆-algebra `A`:

* `spectrum_ge_of_norm_sub_one_le`: `‖a − 1‖ ≤ c` puts `σ(a)` above `1 − c`;
* `exists_conj_eq_one_of_norm_sub_one_le`: for self-adjoint `a` with `‖a − 1‖ ≤ c < 1` there are
  a self-adjoint `g = a^{-1/2}` and an `H` with `g a g = 1` and `g − 1 = (a − 1) H`.

The algebra `StdBdd J` carries a norm, a C⋆-identity and a normed `ℂ`-algebra structure
(`StdOperatorAlgebraNorm`). Given completeness it is a C⋆-algebra
(`StdBdd.cstarAlgebraOfCompleteSpace`), and then
`exists_isometry_compactEq_of_isStdNearIsometry_of_completeSpace` gives the polar correction. The
compactness of `w' − w` is proved in the corona: `π(g) = 1` because `π(w⋆w − 1) = 0`.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section Real

/-- The function `t ↦ (max t δ)^{-1/2}`, equal to `t^{-1/2}` on `[δ, ∞)`
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def isoFixF (δ : ℝ) (t : ℝ) : ℝ := (Real.sqrt (max t δ))⁻¹

/-- The function `h` with `t^{-1/2} − 1 = (t − 1) h(t)` on `[δ, ∞)`
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def isoFixH (δ : ℝ) (t : ℝ) : ℝ :=
  -(Real.sqrt (max t δ) * (1 + Real.sqrt (max t δ)))⁻¹

theorem isoFix_sqrt_max_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < Real.sqrt (max t δ) :=
  Real.sqrt_pos.mpr (lt_of_lt_of_le hδ (le_max_right t δ))

theorem isoFix_continuous_sqrt_max (δ : ℝ) : Continuous fun t : ℝ => Real.sqrt (max t δ) :=
  (continuous_id.max continuous_const).sqrt

/-- `isoFixF δ` is continuous (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem continuous_isoFixF {δ : ℝ} (hδ : 0 < δ) : Continuous (isoFixF δ) := by
  have h := (isoFix_continuous_sqrt_max δ).inv₀ fun t => (isoFix_sqrt_max_pos hδ t).ne'
  exact h

/-- `isoFixH δ` is continuous (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem continuous_isoFixH {δ : ℝ} (hδ : 0 < δ) : Continuous (isoFixH δ) := by
  have hs := isoFix_continuous_sqrt_max δ
  have hp : Continuous fun t : ℝ => Real.sqrt (max t δ) * (1 + Real.sqrt (max t δ)) :=
    hs.mul (continuous_const.add hs)
  have hne : ∀ t : ℝ, Real.sqrt (max t δ) * (1 + Real.sqrt (max t δ)) ≠ 0 := fun t =>
    (mul_pos (isoFix_sqrt_max_pos hδ t) (add_pos zero_lt_one (isoFix_sqrt_max_pos hδ t))).ne'
  have h := (hp.inv₀ hne).neg
  exact h

/-- `s⁻¹ t s⁻¹ = 1` for `s = √t`, `t > 0` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem isoFix_real_conj {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹ = 1 := by
  have hne : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  calc (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹
      = (Real.sqrt t)⁻¹ * (Real.sqrt t * Real.sqrt t) * (Real.sqrt t)⁻¹ := by rw [hss]
    _ = ((Real.sqrt t)⁻¹ * Real.sqrt t) * (Real.sqrt t * (Real.sqrt t)⁻¹) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hne, mul_inv_cancel₀ hne, one_mul]

/-- `s⁻¹ − 1 = (s² − 1) · (−(s(1+s))⁻¹)` for `s > 0` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem isoFix_real_sub_one_aux {s : ℝ} (hs : 0 < s) :
    s⁻¹ - 1 = (s * s - 1) * -(s * (1 + s))⁻¹ := by
  have h1 : (1 + s) ≠ 0 := (add_pos zero_lt_one hs).ne'
  calc s⁻¹ - 1 = s⁻¹ * (1 - s) := by rw [mul_sub, mul_one, inv_mul_cancel₀ hs.ne']
    _ = s⁻¹ * (1 - s) * ((1 + s) * (1 + s)⁻¹) := by rw [mul_inv_cancel₀ h1, mul_one]
    _ = (s * s - 1) * -(s * (1 + s))⁻¹ := by rw [mul_inv]; ring

/-- `t^{-1/2} − 1 = (t − 1) · (−(√t (1 + √t))⁻¹)` for `t > 0` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem isoFix_real_sub_one {t : ℝ} (ht : 0 < t) :
    (Real.sqrt t)⁻¹ - 1 = (t - 1) * -(Real.sqrt t * (1 + Real.sqrt t))⁻¹ := by
  have h := isoFix_real_sub_one_aux (Real.sqrt_pos.mpr ht)
  rwa [Real.mul_self_sqrt ht.le] at h

end Real

section Generic

variable {A : Type*} [CStarAlgebra A]

/-- **Spectrum near `1`.** If `‖a − 1‖ ≤ c` then every `t ∈ σ(a)` satisfies `1 − c ≤ t`
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Murphy Thm. 1.2.8). -/
theorem spectrum_ge_of_norm_sub_one_le {a : A} {c : ℝ} (hac : ‖a - 1‖ ≤ c) {t : ℝ}
    (ht : t ∈ spectrum ℝ a) : 1 - c ≤ t := by
  have ht' : t - 1 ∈ spectrum ℝ (a - 1) := by
    rw [spectrum.mem_iff] at ht ⊢
    have e : algebraMap ℝ A (t - 1) - (a - 1) = algebraMap ℝ A t - a := by
      rw [map_sub, map_one]
      abel
    rwa [e]
  have h1 : ‖(1 : A)‖ ≤ 1 := by
    have hsq : ‖(1 : A)‖ * ‖(1 : A)‖ = ‖(1 : A)‖ := by
      rw [← CStarRing.norm_star_mul_self, star_one, one_mul]
    nlinarith [norm_nonneg (1 : A)]
  have hn : ‖t - 1‖ ≤ ‖a - 1‖ * ‖(1 : A)‖ := spectrum.norm_le_norm_mul_of_mem ht'
  have habs : |t - 1| ≤ c := by
    rw [← Real.norm_eq_abs]
    exact hn.trans ((mul_le_of_le_one_right (norm_nonneg _) h1).trans hac)
  linarith [neg_abs_le (t - 1)]

/-- `a^{-1/2} a a^{-1/2} = 1` when `σ(a) ⊆ [δ, ∞)`, `δ > 0` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Murphy Thm. 2.1.13). -/
theorem cfc_isoFixF_conj (a : A) (ha : IsSelfAdjoint a) {δ : ℝ} (hδ : 0 < δ)
    (hspec : ∀ t ∈ spectrum ℝ a, δ ≤ t) :
    cfc (isoFixF δ) a * a * cfc (isoFixF δ) a = 1 := by
  have hF := continuous_isoFixF hδ
  have e1 := cfc_mul (isoFixF δ) (fun u : ℝ => u) a hF.continuousOn continuousOn_id
  rw [cfc_id' ℝ a ha] at e1
  have e2 := cfc_mul (fun u : ℝ => isoFixF δ u * u) (isoFixF δ) a
    (hF.mul continuous_id).continuousOn hF.continuousOn
  have e3 : cfc (fun u : ℝ => isoFixF δ u * u * isoFixF δ u) a = cfc (fun _ : ℝ => (1 : ℝ)) a := by
    refine cfc_congr ?_
    intro t ht
    have hδt : δ ≤ t := hspec t ht
    show (Real.sqrt (max t δ))⁻¹ * t * (Real.sqrt (max t δ))⁻¹ = 1
    rw [max_eq_left hδt]
    exact isoFix_real_conj (lt_of_lt_of_le hδ hδt)
  rw [← e1, ← e2, e3, cfc_const_one ℝ a ha]

/-- `a^{-1/2} − 1 = (a − 1) h(a)` when `σ(a) ⊆ [δ, ∞)`, `δ > 0` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem cfc_isoFixF_sub_one (a : A) (ha : IsSelfAdjoint a) {δ : ℝ} (hδ : 0 < δ)
    (hspec : ∀ t ∈ spectrum ℝ a, δ ≤ t) :
    cfc (isoFixF δ) a - 1 = (a - 1) * cfc (isoFixH δ) a := by
  have hF := continuous_isoFixF hδ
  have hH := continuous_isoFixH hδ
  have e1 : cfc (fun u : ℝ => (u - 1) * isoFixH δ u) a = (a - 1) * cfc (isoFixH δ) a := by
    rw [cfc_mul (fun u : ℝ => u - 1) (isoFixH δ) a
      (continuous_id.sub continuous_const).continuousOn hH.continuousOn]
    rw [cfc_sub (fun u : ℝ => u) (fun _ : ℝ => (1 : ℝ)) a continuousOn_id continuousOn_const,
      cfc_id' ℝ a ha, cfc_const_one ℝ a ha]
  have e2 : cfc (fun u : ℝ => (u - 1) * isoFixH δ u) a =
      cfc (fun u : ℝ => isoFixF δ u - 1) a := by
    refine cfc_congr ?_
    intro t ht
    have hδt : δ ≤ t := hspec t ht
    show (t - 1) * -(Real.sqrt (max t δ) * (1 + Real.sqrt (max t δ)))⁻¹ =
      (Real.sqrt (max t δ))⁻¹ - 1
    rw [max_eq_left hδt]
    exact (isoFix_real_sub_one (lt_of_lt_of_le hδ hδt)).symm
  have e3 : cfc (fun u : ℝ => isoFixF δ u - 1) a = cfc (isoFixF δ) a - 1 := by
    rw [cfc_sub (isoFixF δ) (fun _ : ℝ => (1 : ℝ)) a hF.continuousOn continuousOn_const,
      cfc_const_one ℝ a ha]
  exact e3.symm.trans (e2.symm.trans e1)

/-- **Inverse square root of an element near `1`.** For self-adjoint `a` with `‖a − 1‖ ≤ c < 1`
there are a self-adjoint `g` (namely `a^{-1/2}`) and an `H` with `g a g = 1` and
`g − 1 = (a − 1) H` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Elliott–Kucerovsky
2001, proof of Thm. 6). -/
theorem exists_conj_eq_one_of_norm_sub_one_le {a : A} (ha : IsSelfAdjoint a) {c : ℝ}
    (hc : c < 1) (hac : ‖a - 1‖ ≤ c) :
    ∃ g H : A, IsSelfAdjoint g ∧ g * a * g = 1 ∧ g - 1 = (a - 1) * H := by
  have hδ : 0 < 1 - c := sub_pos.mpr hc
  have hspec : ∀ t ∈ spectrum ℝ a, 1 - c ≤ t := fun t ht =>
    spectrum_ge_of_norm_sub_one_le hac ht
  exact ⟨cfc (isoFixF (1 - c)) a, cfc (isoFixH (1 - c)) a, IsSelfAdjoint.cfc,
    cfc_isoFixF_conj a ha hδ hspec, cfc_isoFixF_sub_one a ha hδ hspec⟩

end Generic

section Std

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- A complete `StdBdd J` is a unital C⋆-algebra: every other axiom is in
`StdOperatorAlgebraNorm` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
@[reducible] def StdBdd.cstarAlgebraOfCompleteSpace [CompleteSpace (StdBdd J)] :
    CStarAlgebra (StdBdd J) where

/-- The operator bound of `IsStdNearIsometry` is a norm bound (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem StdBdd.norm_star_mul_self_sub_one_le {w : StdBdd J} {c : ℝ}
    (hb : Adjointable.IsBoundedBy (star w * w - 1 : StdBdd J).1 c) :
    ‖(star w * w - 1 : StdBdd J)‖ ≤ max c 0 :=
  (StdBdd.norm_def _).trans_le
    (Adjointable.opNorm_le_of_bound (le_max_right c 0) (hb.mono (le_max_left c 0)))

/-- **Polar correction of a near isometry, given completeness.** If `StdBdd J` is complete, every
near isometry `w` of `H_J` is a compact perturbation of an isometry `w'`, namely
`w' = w (w⋆w)^{-1/2}` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`;
Elliott–Kucerovsky 2001, proof of Thm. 6). -/
theorem exists_isometry_compactEq_of_isStdNearIsometry_of_completeSpace
    [CompleteSpace (StdBdd J)] {w : StdBdd J} (hw : IsStdNearIsometry w) :
    ∃ w' : StdBdd J, star w' * w' = 1 ∧ CompactEq J w'.1 w.1 := by
  obtain ⟨c, hc, hb⟩ := hw.2
  have hac : ‖(star w * w - 1 : StdBdd J)‖ ≤ max c 0 :=
    StdBdd.norm_star_mul_self_sub_one_le hb
  have hk : stdCoronaQuot J (star w * w) = stdCoronaQuot J 1 :=
    (stdCoronaQuot_eq_iff _ _).mpr hw.1
  obtain ⟨g, H, hg, hgag, hg1⟩ := @exists_conj_eq_one_of_norm_sub_one_le (StdBdd J)
    StdBdd.cstarAlgebraOfCompleteSpace (star w * w) (IsSelfAdjoint.star_mul_self w) (max c 0)
    (max_lt hc zero_lt_one) hac
  have hgs : star g = g := hg.star_eq
  have hgag' : g * (star w * w) * g = 1 := hgag
  have hg1' : g - 1 = (star w * w - 1) * H := hg1
  refine ⟨w * g, ?_, ?_⟩
  · calc star (w * g) * (w * g) = g * (star w * w) * g := by
          rw [star_mul, hgs]
          simp only [mul_assoc]
      _ = 1 := hgag'
  · have h0 : stdCoronaQuot J (g - 1) = 0 := by
      rw [hg1', map_mul, map_sub, hk, sub_self, zero_mul]
    have hπg : stdCoronaQuot J g = 1 := by
      rw [map_sub, map_one, sub_eq_zero] at h0
      exact h0
    exact (stdCoronaQuot_eq_iff (w * g) w).mp (by rw [map_mul, hπg, mul_one])

end Std

end GroupApproximation.Full.TWWSchafhauser

end
