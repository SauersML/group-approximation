import GroupApproximation.Algebra.ReturnTowerUnits
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the phase-zero placement

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1754–1755:

> That kernel contains the phase-zero placement of every $g\in K_n(J)$,
> which $\Phi$ sends to $(1-p_C)I_n+g$.

This module is the ring and matrix half of that sentence, for any return tower
`τ : ReturnTowerUnits R N r` (`Algebra/ReturnTowerUnits`) whose zeroth levels are the base
idempotent, `a_0 = b_0 = p_C`.  For the dynamical tower this is `D_0 = C` (tex 1734).

* `IsCornerDeviation τ M`: every entry of `M - 1` lies in the corner `p_C R p_C`.  The unitized
  `K_n(J)` consists of invertible matrices with this property whose deviations lie in `I`;
  `isCornerDeviation_inv` passes the property to inverses.
* `placement τ hr M`: in phase `(0,0)` of the `(i,j)` entry sits `p_C M_ij p_C`, and in the other
  diagonal phases of the diagonal entries the unit of `P_C`.  For `M = (1 - p_C) I_n + g` the phase
  `(0,0)` block is the printed `g ∈ GL_n(P_C)`, so this is its phase-zero placement.
* `unitize_placement`, `unitizeGL_placementUnit`: unitization sends the placement back to `M`
  (printed "which $\Phi$ sends to $(1-p_C)I_n+g$").
* `coe_placement_sub_one_apply`: the deviation of the placement is `M - 1` in phase `(0,0)` and `0`
  elsewhere, so it lies in every ideal containing the entries of `M - 1`.
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open MFQuotientUnits ReturnTowerUnits

variable {R : Type*} [Ring R] {N r : ℕ} (τ : ReturnTowerUnits R N r)
variable {n : Type*} [DecidableEq n]

/-- Every entry of `M - 1` lies in the corner `p_C R p_C`. -/
def IsCornerDeviation (M : Matrix n n R) : Prop :=
  ∀ i j, τ.p * (M - 1) i j = (M - 1) i j ∧ (M - 1) i j * τ.p = (M - 1) i j

/-- `x ↦ p_C x p_C`, into the corner `P_C`. -/
def cornerOf (x : R) : τ.Base :=
  ⟨τ.p * x * τ.p, by
    have hp : τ.p * τ.p = τ.p := τ.isIdempotentElem_p.eq
    rw [mem_cornerNonUnitalSubring_iff]
    constructor
    · calc τ.p * (τ.p * x * τ.p) = (τ.p * τ.p) * x * τ.p := by simp only [mul_assoc]
        _ = τ.p * x * τ.p := by rw [hp]
    · calc τ.p * x * τ.p * τ.p = τ.p * x * (τ.p * τ.p) := by simp only [mul_assoc]
        _ = τ.p * x * τ.p := by rw [hp]⟩

theorem coe_cornerOf (x : R) : (cornerOf τ x : R) = τ.p * x * τ.p :=
  rfl

/-- For a corner deviation, `p_C M_ij p_C = (M - 1)_ij + δ_ij p_C`. -/
theorem p_mul_mul_p_of_isCornerDeviation {M : Matrix n n R} (hM : IsCornerDeviation τ M)
    (i j : n) : τ.p * M i j * τ.p = (M - 1) i j + if i = j then τ.p else 0 := by
  obtain ⟨h1, h2⟩ := hM i j
  have e : M i j = (M - 1) i j + (1 : Matrix n n R) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [e, mul_add, add_mul, h1, h2]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, if_pos rfl, mul_one, τ.isIdempotentElem_p.eq]
  · rw [Matrix.one_apply_ne h, if_neg h, mul_zero, zero_mul]

/-- The inverse of a unit with corner deviation has corner deviation:
`g⁻¹ - 1 = -((g - 1) g⁻¹) = -(g⁻¹ (g - 1))`. -/
theorem isCornerDeviation_inv [Fintype n] {g : (Matrix n n R)ˣ}
    (hg : IsCornerDeviation τ (g : Matrix n n R)) :
    IsCornerDeviation τ (↑g⁻¹ : Matrix n n R) := by
  intro i j
  have hl : (↑g⁻¹ - 1 : Matrix n n R) = -((↑g⁻¹ : Matrix n n R) * (↑g - 1)) := by
    rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
  have hr' : (↑g⁻¹ - 1 : Matrix n n R) = -((↑g - 1) * (↑g⁻¹ : Matrix n n R)) := by
    rw [sub_mul, Units.mul_inv, one_mul, neg_sub]
  constructor
  · rw [hr', Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, (hg i k).1]
  · rw [hl, Matrix.neg_apply, Matrix.mul_apply, neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [mul_assoc, (hg k j).2]

/-- **The phase-zero placement** of `M ∈ M_n(R)` in `M_n(M_r(P_C))`. -/
def placement (hr : 0 < r) (M : Matrix n n R) : Matrix n n (Matrix (Fin r) (Fin r) τ.Base) :=
  Matrix.of fun i j =>
    Matrix.single ⟨0, hr⟩ ⟨0, hr⟩ (cornerOf τ (M i j)) +
      if i = j then 1 - Matrix.single ⟨0, hr⟩ ⟨0, hr⟩ 1 else 0

theorem placement_apply (hr : 0 < r) (M : Matrix n n R) (i j : n) :
    placement τ hr M i j =
      Matrix.single ⟨0, hr⟩ ⟨0, hr⟩ (cornerOf τ (M i j)) +
        if i = j then 1 - Matrix.single ⟨0, hr⟩ ⟨0, hr⟩ 1 else 0 :=
  rfl

theorem phi_single (i₀ j₀ : Fin r) (c : τ.Base) :
    τ.phi (Matrix.single i₀ j₀ c) = τ.a (τ.lo i₀) * (c : R) * τ.b (τ.lo j₀) := by
  rw [phi_apply, Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single j₀]
    · rw [Matrix.single_apply_same]
    · intro j _ hj
      rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj), coe_corner_zero, mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply_of_row_ne (Ne.symm hi), coe_corner_zero, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

theorem phi_placement (hr : 0 < r) (M : Matrix n n R) (i j : n) :
    τ.phi (placement τ hr M i j) =
      τ.a (τ.lo ⟨0, hr⟩) * (τ.p * M i j * τ.p) * τ.b (τ.lo ⟨0, hr⟩) +
        if i = j then τ.phi 1 - τ.a (τ.lo ⟨0, hr⟩) * τ.p * τ.b (τ.lo ⟨0, hr⟩) else 0 := by
  rw [placement_apply, map_add, phi_single, coe_cornerOf]
  split_ifs
  · rw [map_sub, phi_single, coe_cornerOne]
  · rw [map_zero]

/-- **"which $\Phi$ sends to $(1-p_C)I_n+g$"** (tex 1755): unitization sends the phase-zero
placement of a corner deviation back to the matrix. -/
theorem unitize_placement [Fintype n] (hr : 0 < r) (ha : τ.a (τ.lo ⟨0, hr⟩) = τ.p)
    (hb : τ.b (τ.lo ⟨0, hr⟩) = τ.p) {M : Matrix n n R} (hM : IsCornerDeviation τ M) :
    τ.unitize n (placement τ hr M) = M := by
  have hp : τ.p * τ.p = τ.p := τ.isIdempotentElem_p.eq
  refine Matrix.ext fun i j => ?_
  simp only [unitize_apply, Matrix.add_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rw [phi_placement, ha, hb]
  have e3 : τ.p * (τ.p * M i j * τ.p) * τ.p = τ.p * M i j * τ.p := by
    calc τ.p * (τ.p * M i j * τ.p) * τ.p = (τ.p * τ.p) * M i j * (τ.p * τ.p) := by
          simp only [mul_assoc]
      _ = τ.p * M i j * τ.p := by rw [hp]
  rw [e3, p_mul_mul_p_of_isCornerDeviation τ hM i j, Matrix.sub_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, if_pos rfl, hp, hp, Matrix.one_apply_eq]
    abel
  · rw [if_neg h, if_neg h, if_neg h, Matrix.one_apply_ne h]
    abel

/-- The phase-zero placement of a unit with corner deviation, as a unit of `M_n(M_r(P_C))`. -/
def placementUnit [Fintype n] (hr : 0 < r) (ha : τ.a (τ.lo ⟨0, hr⟩) = τ.p)
    (hb : τ.b (τ.lo ⟨0, hr⟩) = τ.p) (g : (Matrix n n R)ˣ)
    (hg : IsCornerDeviation τ (g : Matrix n n R)) :
    (Matrix n n (Matrix (Fin r) (Fin r) τ.Base))ˣ where
  val := placement τ hr (g : Matrix n n R)
  inv := placement τ hr (↑g⁻¹ : Matrix n n R)
  val_inv := τ.unitize_injective n <| by
    rw [map_mul, map_one, unitize_placement τ hr ha hb hg,
      unitize_placement τ hr ha hb (isCornerDeviation_inv τ hg), Units.mul_inv]
  inv_val := τ.unitize_injective n <| by
    rw [map_mul, map_one, unitize_placement τ hr ha hb (isCornerDeviation_inv τ hg),
      unitize_placement τ hr ha hb hg, Units.inv_mul]

theorem coe_placementUnit [Fintype n] (hr : 0 < r) (ha : τ.a (τ.lo ⟨0, hr⟩) = τ.p)
    (hb : τ.b (τ.lo ⟨0, hr⟩) = τ.p) (g : (Matrix n n R)ˣ)
    (hg : IsCornerDeviation τ (g : Matrix n n R)) :
    (placementUnit τ hr ha hb g hg : Matrix n n (Matrix (Fin r) (Fin r) τ.Base)) =
      placement τ hr (g : Matrix n n R) :=
  rfl

/-- **Unitization sends the placement unit back to `g`** (tex 1754–1755). -/
theorem unitizeGL_placementUnit [Fintype n] (hr : 0 < r) (ha : τ.a (τ.lo ⟨0, hr⟩) = τ.p)
    (hb : τ.b (τ.lo ⟨0, hr⟩) = τ.p) (g : (Matrix n n R)ˣ)
    (hg : IsCornerDeviation τ (g : Matrix n n R)) :
    τ.unitizeGL n (placementUnit τ hr ha hb g hg) = g :=
  Units.ext (unitize_placement τ hr ha hb hg)

/-- The deviation of the placement, in `P_C`: `p_C M_ij p_C - δ_ij` in phase `(0,0)`, else `0`. -/
theorem placement_sub_one_apply (hr : 0 < r) (M : Matrix n n R) (i j : n) (a b : Fin r) :
    (placement τ hr M - 1) i j a b =
      if (⟨0, hr⟩ : Fin r) = a ∧ (⟨0, hr⟩ : Fin r) = b then
        cornerOf τ (M i j) - (if i = j then 1 else 0)
      else 0 := by
  rw [Matrix.sub_apply, Matrix.sub_apply, placement_apply, Matrix.add_apply, Matrix.single_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, Matrix.one_apply_eq, Matrix.sub_apply, Matrix.single_apply]
    split_ifs <;> abel
  · rw [if_neg hij, if_neg hij, Matrix.one_apply_ne hij, Matrix.zero_apply]
    split_ifs <;> abel

/-- **The deviation of the placement is `M - 1` in phase `(0,0)` and `0` elsewhere.** -/
theorem coe_placement_sub_one_apply (hr : 0 < r) {M : Matrix n n R}
    (hM : IsCornerDeviation τ M) (i j : n) (a b : Fin r) :
    ((placement τ hr M - 1) i j a b : R) =
      if (⟨0, hr⟩ : Fin r) = a ∧ (⟨0, hr⟩ : Fin r) = b then (M - 1) i j else 0 := by
  rw [placement_sub_one_apply]
  split_ifs with h hij
  · have key := p_mul_mul_p_of_isCornerDeviation τ hM i j
    show τ.p * M i j * τ.p - τ.p = (M - 1) i j
    rw [key, if_pos hij, add_sub_cancel_right]
  · have key := p_mul_mul_p_of_isCornerDeviation τ hM i j
    show τ.p * M i j * τ.p - 0 = (M - 1) i j
    rw [key, if_neg hij, add_zero, sub_zero]
  · rfl

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.p_mul_mul_p_of_isCornerDeviation
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.isCornerDeviation_inv
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.phi_single
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.phi_placement
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.unitize_placement
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.unitizeGL_placementUnit
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.placement_sub_one_apply
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.coe_placement_sub_one_apply
