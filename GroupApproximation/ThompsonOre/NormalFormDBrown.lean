/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.ThompsonOre.NormalFormDMul
import GroupApproximation.ThompsonOre.ThompsonShift

/-!
# The normal form of Brown's group `F_{m+2,∞}` (the presented group `BrownGroup m`)

`BrownGroup m` is Brown's finitely presented `F_{m+2,∞}`; `brownEval m` is faithful on `ℚ`. With
`x_n := X_n⁻¹` (`brownXd`), the relations are `x_j x_i = x_i x_{j+m+1}` (`i < j`), so step `s = m + 1`.

- `brownShift m`: the shift `x_n ↦ x_{n+1}`, which is conjugation by `t ↦ t + 1` through `brownEval`.
  It is injective.
- `chiB m`: the `x_0`-exponent, defined from the presentation.
- `brownFdModel m : FdModel (BrownGroup m) (m + 1)`, and from it `brownF_nf_exists`,
  `brownF_nf_unique` and `brownF_nf_existsUnique`.
- `brownLift`: any family `x : ℕ → G` with `x_j x_i = x_i x_{j+m+1}` gives `BrownGroup m →* G` with
  `x_n ↦ x n` (`brownLift_xd`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.ThompsonOre

open HigmanThompson FdNormal

noncomputable section

variable (m : ℕ)

/-- The generators `x_n = X_n⁻¹` of `F_{m+2,∞}`. -/
def brownXd (n : ℕ) : BrownGroup m := (brownX m n)⁻¹

theorem brownXd_rel {i j : ℕ} (h : i < j) :
    brownXd m j * brownXd m i = brownXd m i * brownXd m (j + (m + 1)) := by
  have h1 := brownX_rel m h
  simp only [brownXd]
  rw [show j + (m + 1) = j + m + 1 by omega, ← h1]
  group

theorem brownXd_closure : Subgroup.closure (Set.range (brownXd m)) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of (brownRels m), Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have h : (PresentedGroup.of i : BrownGroup m) = (brownXd m i.val)⁻¹ := by
    show PresentedGroup.mk (brownRels m) (FreeGroup.of i) = (brownXd m i.val)⁻¹
    rw [brownX_of_fin, brownXd, inv_inv]
  rw [h]
  exact inv_mem (Subgroup.subset_closure ⟨i.val, rfl⟩)

/-! ### The shift -/

theorem conjT_xg_m (k : ℕ) : conjT (xg m k) = xg m (k + 1) := by
  ext t
  simp only [conjT_apply, xg_apply, xfun]
  push_cast
  split_ifs <;> first | ring | (exfalso; linarith)

theorem conjT_brownEval_mem (g : BrownGroup m) : conjT (brownEval m g) ∈ (brownEval m).range := by
  have hle : (⊤ : Subgroup (BrownGroup m)) ≤
      ((brownEval m).range.comap conjT).comap (brownEval m) := by
    rw [← PresentedGroup.closure_range_of (brownRels m), Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show conjT (brownEval m (PresentedGroup.of i)) ∈ (brownEval m).range
    have h : (PresentedGroup.of i : BrownGroup m) = brownX m i.val := brownX_of_fin m i
    rw [h, brownEval_X, conjT_xg_m]
    exact ⟨brownX m (i.val + 1), brownEval_X m _⟩
  exact hle (Subgroup.mem_top g)

/-- The shift `x_n ↦ x_{n+1}` of `F_{m+2,∞}`. -/
def brownShift : BrownGroup m →* BrownGroup m :=
  (MonoidHom.ofInjective (brownEval_injective m)).symm.toMonoidHom.comp
    ((conjT.comp (brownEval m)).codRestrict (brownEval m).range (conjT_brownEval_mem m))

theorem brownEval_brownShift (g : BrownGroup m) :
    brownEval m (brownShift m g) = conjT (brownEval m g) := by
  have h := (MonoidHom.ofInjective (brownEval_injective m)).apply_symm_apply
    ⟨conjT (brownEval m g), conjT_brownEval_mem m g⟩
  have h2 := congrArg Subtype.val h
  rw [MonoidHom.ofInjective_apply] at h2
  exact h2

theorem brownShift_x (n : ℕ) : brownShift m (brownXd m n) = brownXd m (n + 1) := by
  apply brownEval_injective m
  simp only [brownEval_brownShift, brownXd, map_inv, brownEval_X, conjT_xg_m]

theorem brownShift_injective : Function.Injective (brownShift m) := fun a b h =>
  brownEval_injective m (conjT_injective (by rw [← brownEval_brownShift, ← brownEval_brownShift, h]))

/-! ### The `x_0`-exponent -/

/-- `X_0 ↦ -1`, `X_i ↦ 0` for `i ≥ 1`. -/
def chiGen (i : Fin (m + 2)) : Multiplicative ℤ :=
  if i.val = 0 then Multiplicative.ofAdd (-1) else 1

theorem chiGen_brownWord (k : ℕ) :
    FreeGroup.lift (chiGen m) (brownWord m k) = if k = 0 then Multiplicative.ofAdd (-1) else 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : k < m + 2
    · rw [brownWord_of_lt m h, FreeGroup.lift_apply_of, chiGen]
    · rw [brownWord_of_ge m (not_lt.mp h), map_mul, map_mul, map_inv, FreeGroup.lift_apply_of,
        ih (k - (m + 1)) (by omega), if_neg (show ¬ (k - (m + 1) = 0) by omega),
        if_neg (show ¬ (k = 0) by omega), mul_one, mul_inv_cancel]

theorem chiGen_rels : ∀ r ∈ brownRels m, FreeGroup.lift (chiGen m) r = 1 := by
  rintro r ⟨i, j, hi, -, hij, -, rfl⟩
  simp [chiGen_brownWord, show i ≠ 0 by omega, show j ≠ 0 by omega]

/-- The `x_0`-exponent of `F_{m+2,∞}`. -/
def chiB : BrownGroup m →* Multiplicative ℤ := PresentedGroup.toGroup (chiGen_rels m)

theorem chiB_X (k : ℕ) : chiB m (brownX m k) = if k = 0 then Multiplicative.ofAdd (-1) else 1 :=
  chiGen_brownWord m k

theorem chiB_x_zero : chiB m (brownXd m 0) = Multiplicative.ofAdd 1 := by
  rw [brownXd, map_inv, chiB_X, if_pos rfl, ofAdd_neg, inv_inv]

theorem chiB_x_succ (n : ℕ) : chiB m (brownXd m (n + 1)) = 1 := by
  rw [brownXd, map_inv, chiB_X, if_neg (show ¬ (n + 1 = 0) by omega), inv_one]

/-! ### The model and the normal form -/

/-- `F_{m+2,∞}` as an `FdModel` with step `m + 1`. -/
def brownFdModel : FdModel (BrownGroup m) (m + 1) where
  x := brownXd m
  rel _ _ h := brownXd_rel m h
  closure_eq_top := brownXd_closure m
  shift := brownShift m
  shift_x := brownShift_x m
  shift_injective := brownShift_injective m
  chi := chiB m
  chi_x_zero := chiB_x_zero m
  chi_x_succ := chiB_x_succ m

/-- **Existence of the normal form in `F_{m+2,∞}`.** -/
theorem brownF_nf_exists (g : BrownGroup m) : ∃ l, IsNFd (m + 1) l ∧ (brownFdModel m).val l = g :=
  (brownFdModel m).nf_exists g

/-- **Uniqueness of the normal form in `F_{m+2,∞}`.** -/
theorem brownF_nf_unique {l l' : List (ℕ × ℕ)} (hl : IsNFd (m + 1) l) (hl' : IsNFd (m + 1) l')
    (h : (brownFdModel m).val l = (brownFdModel m).val l') : l = l' :=
  (brownFdModel m).nf_unique l l' hl hl' h

theorem brownF_nf_existsUnique (g : BrownGroup m) :
    ∃! l, IsNFd (m + 1) l ∧ (brownFdModel m).val l = g :=
  (brownFdModel m).nf_existsUnique g

/-! ### The lift -/

section Lift

variable {m} {G : Type*} [Group G] (x : ℕ → G)
  (hrel : ∀ i j : ℕ, i < j → x j * x i = x i * x (j + (m + 1)))

include hrel

theorem lift_brownWord_xd (k : ℕ) :
    FreeGroup.lift (fun i : Fin (m + 2) => (x i.val)⁻¹) (brownWord m k) = (x k)⁻¹ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : k < m + 2
    · rw [brownWord_of_lt m h, FreeGroup.lift_apply_of]
    · have h0 : FreeGroup.lift (fun i : Fin (m + 2) => (x i.val)⁻¹)
          (FreeGroup.of ⟨0, by omega⟩) = (x 0)⁻¹ := FreeGroup.lift_apply_of
      rw [brownWord_of_ge m (not_lt.mp h), map_mul, map_mul, map_inv, h0,
        ih (k - (m + 1)) (by omega)]
      have e := hrel 0 (k - (m + 1)) (by omega)
      rw [show k - (m + 1) + (m + 1) = k by omega] at e
      have e2 : x k = (x 0)⁻¹ * x (k - (m + 1)) * x 0 := by
        rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e2]
      group

theorem brownLift_rels :
    ∀ r ∈ brownRels m, FreeGroup.lift (fun i : Fin (m + 2) => (x i.val)⁻¹) r = 1 := by
  rintro r ⟨i, j, -, -, hij, -, rfl⟩
  simp only [map_mul, map_inv, lift_brownWord_xd x hrel]
  have e := hrel i j hij
  rw [show j + (m + 1) = j + m + 1 by omega] at e
  have e2 : x (j + m + 1) = (x i)⁻¹ * x j * x i := by
    rw [mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [e2]
  group

/-- **The lift**: a family with `x_j x_i = x_i x_{j+m+1}` defines `BrownGroup m →* G`. -/
def brownLift : BrownGroup m →* G := PresentedGroup.toGroup (brownLift_rels x hrel)

theorem brownLift_X (k : ℕ) : brownLift x hrel (brownX m k) = (x k)⁻¹ :=
  lift_brownWord_xd x hrel k

theorem brownLift_xd (n : ℕ) : brownLift x hrel (brownXd m n) = x n := by
  rw [brownXd, map_inv, brownLift_X, inv_inv]

end Lift

end

end GroupApproximation.ThompsonOre
