import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Compactness of `T` from compactness of `T*T`

Lane `TWWSch-Inv3`, work order `WO-Inv-3` of `TWWSch3d2Inv`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through the Busby picture of `Ext(S, J)` used in
Schafhauser's proof of the Tikuisis--White--Winter theorem. The result is used to show that the
`(2,1)` corner of a Stinespring dilation is compact.

**Theorem** (Lance, *Hilbert C⋆-modules*, Ch. 1--2; Blackadar, *Operator Algebras*, II.5.1.1).
If `T` is a bounded adjointable operator on `H_J` and `T*T` is compact, then `T` is compact.

**Proof.** We do not use polar decomposition. Work in the C⋆-algebra `StdBdd J` of bounded
adjointable operators, with `a = T` and `b = a⋆a`. For `δ > 0`, put
`g(t) = t / (t² + δ²)` and `e(t) = δ² / (t² + δ²)`, so that `t g(t) = 1 - e(t)`. The operator
`K = a (b g(b))` is compact, because `b` is. Also `a - K = a e(b)`. The C⋆-identity gives
`‖a e(b)‖² = ‖e(b) b e(b)‖ = ‖(t e(t)²)(b)‖ ≤ sup_t |t| e(t)² ≤ δ`, since `2|t|δ ≤ t² + δ²`.
Take `δ = ε²`. The functions are continuous on all of `ℝ`, so we never need `σ(b) ⊆ [0, ∞)`.
Close with `Adjointable.isCompactOp_of_approx`: the compact operators are norm-closed.

* `compactApproxErr`, `compactApproxInv`: the real functions `e` and `g`;
* `abs_compactApproxErr_mul_le`: `|e(t) t e(t)| ≤ δ`;
* `StdBdd.norm_sub_mul_cfc_le`: `‖a - a (b g(b))‖² ≤ δ` when `b = a⋆a`;
* **`isCompactOp_of_isCompactOp_adjoint_comp_self`**.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

noncomputable section

/-- The error function `e(t) = δ² / (t² + δ²)` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Lance Ch. 1--2). -/
def compactApproxErr (δ t : ℝ) : ℝ := δ ^ 2 / (t ^ 2 + δ ^ 2)

/-- The approximate inverse `g(t) = t / (t² + δ²)` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Lance Ch. 1--2). -/
def compactApproxInv (δ t : ℝ) : ℝ := t / (t ^ 2 + δ ^ 2)

/-- The common denominator is positive (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem compactApprox_denom_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < t ^ 2 + δ ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg t) (pow_pos hδ 2)

/-- The function `t ↦ t² + δ²` is continuous (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem continuous_compactApprox_denom (δ : ℝ) : Continuous fun t : ℝ => t ^ 2 + δ ^ 2 :=
  (continuous_pow 2).add continuous_const

/-- `e` is continuous on all of `ℝ` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem continuous_compactApproxErr {δ : ℝ} (hδ : 0 < δ) : Continuous (compactApproxErr δ) := by
  show Continuous fun t : ℝ => δ ^ 2 / (t ^ 2 + δ ^ 2)
  exact continuous_const.div₀ (continuous_compactApprox_denom δ) fun t =>
    (compactApprox_denom_pos hδ t).ne'

/-- `g` is continuous on all of `ℝ` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem continuous_compactApproxInv {δ : ℝ} (hδ : 0 < δ) : Continuous (compactApproxInv δ) := by
  show Continuous fun t : ℝ => t / (t ^ 2 + δ ^ 2)
  exact continuous_id'.div₀ (continuous_compactApprox_denom δ) fun t =>
    (compactApprox_denom_pos hδ t).ne'

/-- `1 - e(t) = t g(t)` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem one_sub_compactApproxErr {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    1 - compactApproxErr δ t = t * compactApproxInv δ t := by
  show 1 - δ ^ 2 / (t ^ 2 + δ ^ 2) = t * (t / (t ^ 2 + δ ^ 2))
  rw [mul_div_assoc', one_sub_div (compactApprox_denom_pos hδ t).ne']
  congr 1
  ring

/-- The scalar estimate `|e(t) t e(t)| ≤ δ`, from `2|t|δ ≤ t² + δ²` (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
theorem abs_compactApproxErr_mul_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |compactApproxErr δ t * t * compactApproxErr δ t| ≤ δ := by
  have hs : 0 < t ^ 2 + δ ^ 2 := compactApprox_denom_pos hδ t
  have he0 : 0 ≤ compactApproxErr δ t := div_nonneg (sq_nonneg δ) hs.le
  have he1 : compactApproxErr δ t ≤ 1 := by
    show δ ^ 2 / (t ^ 2 + δ ^ 2) ≤ 1
    exact (div_le_one₀ hs).mpr (le_add_of_nonneg_left (sq_nonneg t))
  have hte : |t| * compactApproxErr δ t ≤ δ := by
    have h2 : 2 * |t| * δ ≤ t ^ 2 + δ ^ 2 := by
      have h := two_mul_le_add_sq |t| δ
      rwa [sq_abs] at h
    have h3 := mul_le_mul_of_nonneg_left h2 hδ.le
    have h4 : 0 ≤ |t| * δ ^ 2 := mul_nonneg (abs_nonneg t) (sq_nonneg δ)
    show |t| * (δ ^ 2 / (t ^ 2 + δ ^ 2)) ≤ δ
    rw [mul_div_assoc', div_le_iff₀ hs]
    nlinarith [h3, h4]
  rw [abs_mul, abs_mul, abs_of_nonneg he0, mul_assoc]
  exact (mul_le_of_le_one_left (mul_nonneg (abs_nonneg t) he0) he1).trans hte

section Estimate

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **The approximation estimate.** If `b = a⋆a` in `StdBdd J`, then
`‖a - a (b g(b))‖² ≤ δ` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Lance
Ch. 1--2). -/
theorem StdBdd.norm_sub_mul_cfc_le (a b : StdBdd J) (hab : star a * a = b) {δ : ℝ}
    (hδ : 0 < δ) : ‖a - a * (b * cfc (compactApproxInv δ) b)‖ ^ 2 ≤ δ := by
  have hb : IsSelfAdjoint b := by
    rw [← hab]
    exact IsSelfAdjoint.star_mul_self a
  have hcE := continuous_compactApproxErr hδ
  have hcI := continuous_compactApproxInv hδ
  have h1 : b * cfc (compactApproxInv δ) b = 1 - cfc (compactApproxErr δ) b := by
    calc b * cfc (compactApproxInv δ) b
        = cfc (fun t : ℝ => t) b * cfc (compactApproxInv δ) b := by rw [cfc_id' ℝ b hb]
      _ = cfc (fun t : ℝ => t * compactApproxInv δ t) b :=
          (cfc_mul (fun t : ℝ => t) (compactApproxInv δ) b continuous_id'.continuousOn
            hcI.continuousOn).symm
      _ = cfc (fun t : ℝ => 1 - compactApproxErr δ t) b := by
          rw [show (fun t : ℝ => t * compactApproxInv δ t) =
              (fun t : ℝ => 1 - compactApproxErr δ t) from
            funext fun t => (one_sub_compactApproxErr hδ t).symm]
      _ = cfc (fun _ : ℝ => (1 : ℝ)) b - cfc (compactApproxErr δ) b :=
          cfc_sub (fun _ : ℝ => (1 : ℝ)) (compactApproxErr δ) b continuousOn_const
            hcE.continuousOn
      _ = 1 - cfc (compactApproxErr δ) b := by rw [cfc_const_one ℝ b hb]
  have hr : IsSelfAdjoint (cfc (compactApproxErr δ) b) := cfc_predicate (compactApproxErr δ) b
  have h2 : a - a * (b * cfc (compactApproxInv δ) b) = a * cfc (compactApproxErr δ) b := by
    rw [h1, mul_sub, mul_one, sub_sub_cancel]
  have h3 : star (a * cfc (compactApproxErr δ) b) * (a * cfc (compactApproxErr δ) b) =
      cfc (compactApproxErr δ) b * b * cfc (compactApproxErr δ) b := by
    calc star (a * cfc (compactApproxErr δ) b) * (a * cfc (compactApproxErr δ) b)
        = cfc (compactApproxErr δ) b * (star a * a) * cfc (compactApproxErr δ) b := by
          rw [star_mul, hr.star_eq]
          simp only [mul_assoc]
      _ = cfc (compactApproxErr δ) b * b * cfc (compactApproxErr δ) b := by rw [hab]
  have h4 : cfc (compactApproxErr δ) b * b * cfc (compactApproxErr δ) b =
      cfc (fun t : ℝ => compactApproxErr δ t * t * compactApproxErr δ t) b := by
    calc cfc (compactApproxErr δ) b * b * cfc (compactApproxErr δ) b
        = cfc (compactApproxErr δ) b * cfc (fun t : ℝ => t) b * cfc (compactApproxErr δ) b := by
          rw [cfc_id' ℝ b hb]
      _ = cfc (fun t : ℝ => compactApproxErr δ t * t) b * cfc (compactApproxErr δ) b := by
          rw [← cfc_mul (compactApproxErr δ) (fun t : ℝ => t) b hcE.continuousOn
            continuous_id'.continuousOn]
      _ = cfc (fun t : ℝ => compactApproxErr δ t * t * compactApproxErr δ t) b :=
          (cfc_mul (fun t : ℝ => compactApproxErr δ t * t) (compactApproxErr δ) b
            (hcE.mul continuous_id').continuousOn hcE.continuousOn).symm
  have h5 : ‖cfc (fun t : ℝ => compactApproxErr δ t * t * compactApproxErr δ t) b‖ ≤ δ :=
    norm_cfc_le hδ.le fun t _ =>
      (Real.norm_eq_abs _).trans_le (abs_compactApproxErr_mul_le hδ t)
  rw [h2, sq, ← CStarRing.norm_star_mul_self, h3, h4]
  exact h5

end Estimate

/-- **WO-Inv-3.** A bounded operator `T` on `H_J` with `T*T` compact is compact
(`non_mf_group_notes.tex`, `thm:fixed-radical-membership`; Lance, *Hilbert C⋆-modules*,
Ch. 1--2; Blackadar, *Operator Algebras*, II.5.1.1). -/
theorem isCompactOp_of_isCompactOp_adjoint_comp_self {J : Type} [NonUnitalCStarAlgebra J]
    [PartialOrder J] [StarOrderedRing J] {T : StdOp J} (hT : T.IsBounded)
    (h : (Adjointable.comp (Adjointable.adjoint T) T).IsCompactOp) : T.IsCompactOp := by
  refine Adjointable.isCompactOp_of_approx hT fun ε hε => ?_
  let a : StdBdd J := ⟨T, mem_boundedAdj.mpr hT⟩
  let c : StdBdd J := cfc (compactApproxInv (ε ^ 2)) (star a * a)
  refine ⟨(a * (star a * a * c)).1, ?_, ?_⟩
  · exact (h.comp_right (StdBdd.isBounded c)).comp_left hT
  · have hn : ‖a - a * (star a * a * c)‖ ^ 2 ≤ ε ^ 2 :=
      StdBdd.norm_sub_mul_cfc_le a (star a * a) rfl (pow_pos hε 2)
    have hn' : ‖a - a * (star a * a * c)‖ ≤ ε := (sq_le_sq₀ (norm_nonneg _) hε.le).mp hn
    exact (Adjointable.isBoundedBy_opNorm (StdBdd.isBounded (a - a * (star a * a * c)))).mono hn'

end

end GroupApproximation.Full.TWWSchafhauser
