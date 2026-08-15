import GroupApproximation.Monsters.P13WeylFourthPowers
import GroupApproximation.Monsters.P13LowerUnipotentInjectivity

/-!
# The canonical column lift in the P13 presentation

The completeness programme reduces the injectivity of
`toSL3 : P13 →* SL₃(ℤ)` to the containment of its kernel in the
parabolic subgroup `⟨e₁₂, e₂₁, e₃₁, e₃₂⟩`.  This file builds the
transversal machinery for that containment: for every integer column
`v` a canonical word `rho v` in the presented group whose matrix drags
`v` to the third basis column `e₃`, by a Euclidean descent through the
`13`- and `23`-root subgroups with the signed swaps `w13`, `w23`
performing the exchanges.  The descent measure is `|v 0| + |v 1|`, a
plain natural number that each step strictly decreases.

The inverse `m v := (rho v)⁻¹` is the canonical lift of `v`: its
matrix carries `e₃` to `v`, and `m e₃ = 1`.  The final section
introduces the associated cocycle
`sigma g v = rho (g·v) * g * (rho v)⁻¹`, whose value measures the
failure of `g · m v` to be the canonical lift of `g·v`; along the
canonical descent the cocycle is trivial by construction.  The
membership of all generator cocycles in the parabolic subgroup is the
remaining containment step and is proved in later files.
-/

namespace GroupApproximation
namespace P13ColumnLift

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open SL3ElementaryGeneration P13UnipotentInjectivity
open P13LowerUnipotentInjectivity
open P13WeylCalculus P13Weyl13Calculus P13Weyl23Calculus

noncomputable section

/-! ## Columns and the matrix action -/

/-- The third standard basis column. -/
def e3 : Fin 3 → ℤ := ![0, 0, 1]

/-- Componentwise extensionality for integer columns. -/
theorem vec3_ext {v w : Fin 3 → ℤ} (h0 : v 0 = w 0) (h1 : v 1 = w 1)
    (h2 : v 2 = w 2) : v = w := by
  funext k
  match k with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

/-- The left action of a special linear matrix on integer columns. -/
def act (M : SL3) (v : Fin 3 → ℤ) : Fin 3 → ℤ := M.val.mulVec v

theorem act_apply (M : SL3) (v : Fin 3 → ℤ) (k : Fin 3) :
    act M v k = M.val k 0 * v 0 + M.val k 1 * v 1 + M.val k 2 * v 2 := by
  simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem act_mul (M N : SL3) (v : Fin 3 → ℤ) :
    act (M * N) v = act M (act N v) := by
  simp [act, Matrix.mulVec_mulVec]

theorem act_one (v : Fin 3 → ℤ) : act 1 v = v := by
  simp [act]

theorem act_e3_apply (M : SL3) (k : Fin 3) : act M e3 k = M.val k 2 := by
  simp [act_apply, e3]

/-! ## The action of the root elements and the signed swaps -/

theorem act_x0 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 0 c)) v = ![v 0 + c * v 1, v 1, v 2] := by
  have h : toSL3 (x 0 c) = tv 0 1 (by decide) c := by
    rw [toSL3_x, elem0_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]

theorem act_x1 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 1 c)) v = ![v 0 + c * v 2, v 1, v 2] := by
  have h : toSL3 (x 1 c) = tv 0 2 (by decide) c := by
    rw [toSL3_x, elem1_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]

theorem act_x2 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 2 c)) v = ![v 0, v 1 + c * v 0, v 2] := by
  have h : toSL3 (x 2 c) = tv 1 0 (by decide) c := by
    rw [toSL3_x, elem2_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]
  ring

theorem act_x3 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 3 c)) v = ![v 0, v 1 + c * v 2, v 2] := by
  have h : toSL3 (x 3 c) = tv 1 2 (by decide) c := by
    rw [toSL3_x, elem3_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]

theorem act_x4 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 4 c)) v = ![v 0, v 1, v 2 + c * v 0] := by
  have h : toSL3 (x 4 c) = tv 2 0 (by decide) c := by
    rw [toSL3_x, elem4_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]
  ring

theorem act_x5 (c : ℤ) (v : Fin 3 → ℤ) :
    act (toSL3 (x 5 c)) v = ![v 0, v 1, v 2 + c * v 1] := by
  have h : toSL3 (x 5 c) = tv 2 1 (by decide) c := by
    rw [toSL3_x, elem5_zpow]
  refine vec3_ext ?_ ?_ ?_ <;>
    simp [h, act_apply, Matrix.transvection, Matrix.single,
      Matrix.add_apply, Matrix.of_apply]
  ring

theorem toSL3_w13 :
    toSL3 w13 = ⟨!![0, 0, 1; 0, 1, 0; -1, 0, 0], by decide⟩ := by
  show toSL3 (x 1 1 * x 4 (-1) * x 1 1) = _
  rw [map_mul, map_mul, toSL3_x, toSL3_x, elem1_zpow, elem4_zpow]
  apply Subtype.ext
  decide

theorem toSL3_w23 :
    toSL3 w23 = ⟨!![1, 0, 0; 0, 0, 1; 0, -1, 0], by decide⟩ := by
  show toSL3 (x 3 1 * x 5 (-1) * x 3 1) = _
  rw [map_mul, map_mul, toSL3_x, toSL3_x, elem3_zpow, elem5_zpow]
  apply Subtype.ext
  decide

theorem act_w13 (v : Fin 3 → ℤ) :
    act (toSL3 w13) v = ![v 2, v 1, -(v 0)] := by
  refine vec3_ext ?_ ?_ ?_ <;> simp [toSL3_w13, act_apply]

theorem act_w23 (v : Fin 3 → ℤ) :
    act (toSL3 w23) v = ![v 0, v 2, -(v 1)] := by
  refine vec3_ext ?_ ?_ ?_ <;> simp [toSL3_w23, act_apply]

/-! ## Unimodular columns -/

/-- The columns realized as third columns of special linear matrices. -/
def IsColumn (v : Fin 3 → ℤ) : Prop := ∃ M : SL3, act M e3 = v

theorem isColumn_e3 : IsColumn e3 := ⟨1, act_one e3⟩

theorem IsColumn.act {v : Fin 3 → ℤ} (hv : IsColumn v) (N : SL3) :
    IsColumn (P13ColumnLift.act N v) := by
  obtain ⟨M, hM⟩ := hv
  exact ⟨N * M, by rw [act_mul, hM]⟩

/-- A column supported in the last coordinate is unimodular there:
the determinant expansion shows the last entry divides `1`. -/
theorem isColumn_base {v : Fin 3 → ℤ} (hv : IsColumn v)
    (h0 : v 0 = 0) (h1 : v 1 = 0) : v 2 = 1 ∨ v 2 = -1 := by
  obtain ⟨M, hM⟩ := hv
  have e0 : M.val 0 2 = 0 := by
    rw [← act_e3_apply M 0, hM]; exact h0
  have e1 : M.val 1 2 = 0 := by
    rw [← act_e3_apply M 1, hM]; exact h1
  have e2 : M.val 2 2 = v 2 := by
    rw [← act_e3_apply M 2, hM]
  have hdet : M.val.det = 1 := M.property
  rw [Matrix.det_fin_three] at hdet
  rw [e0, e1, e2] at hdet
  have hdvd : v 2 ∣ 1 :=
    ⟨M.val 0 0 * M.val 1 1 - M.val 0 1 * M.val 1 0, by linarith [hdet]⟩
  exact Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd)

/-! ## The Euclidean descent -/

/-- The remainder of division by a nonzero integer is smaller in
absolute value.  (`omega` cannot see this: the divisor is a
variable.) -/
theorem natAbs_emod_lt (a b : ℤ) (hb : b ≠ 0) :
    (a % b).natAbs < b.natAbs := by
  have h0 : 0 ≤ a % b := Int.emod_nonneg a hb
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have h1 : a % b < -b := by
      have h2 := Int.emod_lt_of_pos a (by omega : (0 : ℤ) < -b)
      rwa [Int.emod_neg] at h2
    omega
  · have h1 : a % b < b := Int.emod_lt_of_pos a hpos
    omega

/-- The descent measure. -/
def euclidMeas (v : Fin 3 → ℤ) : ℕ := (v 0).natAbs + (v 1).natAbs

/-- The canonical reduction word: its matrix drags `v` to `e₃`.
Phase A (first coordinate nonzero) reduces through the `13`-block,
phase B through the `23`-block, and phase C fixes the sign. -/
def rho (v : Fin 3 → ℤ) : P13 :=
  if _h0 : v 0 = 0 then
    if _h1 : v 1 = 0 then
      if v 2 < 0 then w13 * w13 else 1
    else
      rho ![v 0, v 2 % v 1, -(v 1)] * (w23 * x 5 (-(v 2 / v 1)))
  else
    rho ![v 2 % v 0, v 1, -(v 0)] * (w13 * x 4 (-(v 2 / v 0)))
  termination_by euclidMeas v
  decreasing_by
  · simp only [euclidMeas, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h := natAbs_emod_lt (v 2) (v 1) _h1
    omega
  · simp only [euclidMeas, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h := natAbs_emod_lt (v 2) (v 0) _h0
    omega

theorem rho_A (v : Fin 3 → ℤ) (h0 : v 0 ≠ 0) :
    rho v = rho ![v 2 % v 0, v 1, -(v 0)] * (w13 * x 4 (-(v 2 / v 0))) := by
  rw [rho.eq_def, dif_neg h0]

theorem rho_B (v : Fin 3 → ℤ) (h0 : v 0 = 0) (h1 : v 1 ≠ 0) :
    rho v = rho ![v 0, v 2 % v 1, -(v 1)] * (w23 * x 5 (-(v 2 / v 1))) := by
  rw [rho.eq_def, dif_pos h0, dif_neg h1]

theorem rho_C (v : Fin 3 → ℤ) (h0 : v 0 = 0) (h1 : v 1 = 0) :
    rho v = if v 2 < 0 then w13 * w13 else 1 := by
  rw [rho.eq_def, dif_pos h0, dif_pos h1]

/-- The matrix action of the phase-A step. -/
theorem stepA_act (v : Fin 3 → ℤ) :
    act (toSL3 (w13 * x 4 (-(v 2 / v 0)))) v =
      ![v 2 % v 0, v 1, -(v 0)] := by
  rw [map_mul, act_mul, act_x4, act_w13]
  refine vec3_ext ?_ ?_ ?_
  · simp
    rw [Int.emod_def]
    ring
  · simp
  · simp

/-- The matrix action of the phase-B step. -/
theorem stepB_act (v : Fin 3 → ℤ) :
    act (toSL3 (w23 * x 5 (-(v 2 / v 1)))) v =
      ![v 0, v 2 % v 1, -(v 1)] := by
  rw [map_mul, act_mul, act_x5, act_w23]
  refine vec3_ext ?_ ?_ ?_
  · simp
  · simp
    rw [Int.emod_def]
    ring
  · simp

private theorem rho_spec_aux :
    ∀ (n : ℕ) (v : Fin 3 → ℤ), euclidMeas v < n → IsColumn v →
      act (toSL3 (rho v)) v = e3 := by
  intro n
  induction n with
  | zero => exact fun v h _ => absurd h (Nat.not_lt_zero _)
  | succ n IH =>
      intro v hn hv
      by_cases h0 : v 0 = 0
      · by_cases h1 : v 1 = 0
        · -- phase C
          rw [rho_C v h0 h1]
          rcases isColumn_base hv h0 h1 with h2 | h2
          · rw [if_neg (by omega : ¬ v 2 < 0), map_one, act_one]
            exact vec3_ext (by simp [e3, h0]) (by simp [e3, h1])
              (by simp [e3, h2])
          · rw [if_pos (by omega : v 2 < 0), map_mul, act_mul, act_w13,
              act_w13]
            refine vec3_ext ?_ ?_ ?_ <;> simp [e3, h0, h1, h2]
        · -- phase B
          rw [rho_B v h0 h1, map_mul, act_mul, stepB_act]
          have hcol : IsColumn ![v 0, v 2 % v 1, -(v 1)] := by
            have h := hv.act (toSL3 (w23 * x 5 (-(v 2 / v 1))))
            rwa [stepB_act] at h
          have hlt : euclidMeas ![v 0, v 2 % v 1, -(v 1)] < n := by
            simp only [euclidMeas, Matrix.cons_val_zero,
              Matrix.cons_val_one] at hn ⊢
            have h := natAbs_emod_lt (v 2) (v 1) h1
            omega
          exact IH _ hlt hcol
      · -- phase A
        rw [rho_A v h0, map_mul, act_mul, stepA_act]
        have hcol : IsColumn ![v 2 % v 0, v 1, -(v 0)] := by
          have h := hv.act (toSL3 (w13 * x 4 (-(v 2 / v 0))))
          rwa [stepA_act] at h
        have hlt : euclidMeas ![v 2 % v 0, v 1, -(v 0)] < n := by
          simp only [euclidMeas, Matrix.cons_val_zero,
            Matrix.cons_val_one] at hn ⊢
          have h := natAbs_emod_lt (v 2) (v 0) h0
          omega
        exact IH _ hlt hcol

/-- **Reduction specification.**  The canonical word drags every
unimodular column to the third basis column. -/
theorem rho_spec (v : Fin 3 → ℤ) (hv : IsColumn v) :
    act (toSL3 (rho v)) v = e3 :=
  rho_spec_aux (euclidMeas v + 1) v (Nat.lt_succ_self _) hv

theorem rho_e3 : rho e3 = 1 := by
  rw [rho_C e3 (by simp [e3]) (by simp [e3])]
  simp [e3]

/-! ## The canonical lift -/

/-- The canonical lift of a column: its matrix carries `e₃` to `v`. -/
def m (v : Fin 3 → ℤ) : P13 := (rho v)⁻¹

theorem m_e3 : m e3 = 1 := by
  rw [m, rho_e3, inv_one]

/-- **Lift specification.** -/
theorem m_spec (v : Fin 3 → ℤ) (hv : IsColumn v) :
    act (toSL3 (m v)) e3 = v := by
  have h := rho_spec v hv
  have h2 : act ((toSL3 (rho v))⁻¹) (act (toSL3 (rho v)) v) = v := by
    rw [← act_mul, inv_mul_cancel, act_one]
  rw [h] at h2
  rw [m, map_inv]
  exact h2

/-! ## The transversal cocycle -/

/-- The cocycle measuring the failure of `g · m v` to be canonical. -/
def sigma (g : P13) (v : Fin 3 → ℤ) : P13 :=
  rho (act (toSL3 g) v) * g * (rho v)⁻¹

theorem sigma_mul (g h : P13) (v : Fin 3 → ℤ) :
    sigma (g * h) v = sigma g (act (toSL3 h) v) * sigma h v := by
  unfold sigma
  rw [map_mul, act_mul]
  group

theorem sigma_one (v : Fin 3 → ℤ) : sigma 1 v = 1 := by
  unfold sigma
  rw [map_one, act_one]
  group

/-- The factorization carried by the cocycle: multiplication by `g`
moves the canonical lift of `v` to the canonical lift of `g·v` up to
the cocycle value. -/
theorem mul_m_eq (g : P13) (v : Fin 3 → ℤ) :
    g * m v = m (act (toSL3 g) v) * sigma g v := by
  unfold sigma m
  group

/-- Along the canonical phase-A descent the cocycle is trivial. -/
theorem sigma_stepA (v : Fin 3 → ℤ) (h0 : v 0 ≠ 0) :
    sigma (w13 * x 4 (-(v 2 / v 0))) v = 1 := by
  unfold sigma
  rw [stepA_act, rho_A v h0]
  group

/-- Along the canonical phase-B descent the cocycle is trivial. -/
theorem sigma_stepB (v : Fin 3 → ℤ) (h0 : v 0 = 0) (h1 : v 1 ≠ 0) :
    sigma (w23 * x 5 (-(v 2 / v 1))) v = 1 := by
  unfold sigma
  rw [stepB_act, rho_B v h0 h1]
  group

end

end P13ColumnLift
end GroupApproximation
