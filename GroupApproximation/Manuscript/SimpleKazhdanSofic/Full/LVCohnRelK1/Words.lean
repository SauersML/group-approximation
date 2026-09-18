import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Cohn

/-!
# Matrix units in the Cohn algebra

For words `μ, ν` over `{0,1}` put `x_μ = x_{μ₁} ⋯ x_{μ_k}`, `y_ν = y_{ν_k} ⋯ y_{ν₁}` and
`p = 1 - x₀y₀ - x₁y₁`.  The elements `e_{μν} = x_μ p y_ν` of `C₂(𝔽₂)` form a system of
matrix units, `e_{μν} e_{αβ} = δ_{να} e_{μβ}`.  They span the kernel of `C₂(𝔽₂) → L_{𝔽₂}(1,2)`,
an ideal isomorphic to `M_∞(𝔽₂)` (Ara-Brustenga-Cortiñas 2009).  This is the algebraic input
to step W1 of `simple_kazhdan_sofic_group.tex` l.733-735.
-/

namespace GroupApproximation.Full.LVCohnRelK1

noncomputable section

/-- The monomial `x_μ` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
def xw : List Bool → CohnTwoF2
  | [] => 1
  | i :: μ => cx i * xw μ

/-- The monomial `y_ν`, written so that `y_ν x_ν = 1`. -/
def yw : List Bool → CohnTwoF2
  | [] => 1
  | i :: ν => yw ν * cy i

theorem xw_nil : xw [] = 1 := rfl

theorem xw_cons (i : Bool) (μ : List Bool) : xw (i :: μ) = cx i * xw μ := rfl

theorem yw_nil : yw [] = 1 := rfl

theorem yw_cons (i : Bool) (ν : List Bool) : yw (i :: ν) = yw ν * cy i := rfl

/-- The projection `p = 1 - x₀y₀ - x₁y₁` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
def cohnP : CohnTwoF2 := 1 - cx false * cy false - cx true * cy true

theorem cohnP_def : cohnP = 1 - cx false * cy false - cx true * cy true := rfl

/-- The matrix unit `e_{μν} = x_μ p y_ν` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
def unitE (μ ν : List Bool) : CohnTwoF2 := xw μ * cohnP * yw ν

theorem unitE_def (μ ν : List Bool) : unitE μ ν = xw μ * cohnP * yw ν := rfl

theorem cohnP_cx (i : Bool) : cohnP * cx i = 0 := by
  cases i with
  | false =>
    rw [cohnP_def, sub_mul, sub_mul, one_mul, mul_assoc, mul_assoc, y0_x0, y1_x0,
      mul_one, mul_zero, sub_self, sub_zero]
  | true =>
    rw [cohnP_def, sub_mul, sub_mul, one_mul, mul_assoc, mul_assoc, y0_x1, y1_x1,
      mul_one, mul_zero, sub_zero, sub_self]

theorem cy_cohnP (i : Bool) : cy i * cohnP = 0 := by
  cases i with
  | false =>
    rw [cohnP_def, mul_sub, mul_sub, mul_one, ← mul_assoc, ← mul_assoc, y0_x0, y0_x1,
      one_mul, zero_mul, sub_self, sub_zero]
  | true =>
    rw [cohnP_def, mul_sub, mul_sub, mul_one, ← mul_assoc, ← mul_assoc, y1_x0, y1_x1,
      one_mul, zero_mul, sub_zero, sub_self]

theorem cohnP_mul_self : cohnP * cohnP = cohnP := by
  have h1 : cohnP * (cx false * cy false) = 0 := by
    rw [← mul_assoc, cohnP_cx, zero_mul]
  have h2 : cohnP * (cx true * cy true) = 0 := by
    rw [← mul_assoc, cohnP_cx, zero_mul]
  calc cohnP * cohnP = cohnP * (1 - cx false * cy false - cx true * cy true) := rfl
    _ = cohnP := by rw [mul_sub, mul_sub, mul_one, h1, h2, sub_zero, sub_zero]

theorem yx_assoc (ν α : List Bool) (i j : Bool) :
    yw ν * cy i * (cx j * xw α) = yw ν * (cy i * cx j) * xw α := by
  simp only [mul_assoc]

theorem cohnP_yx_cohnP_self : ∀ ν : List Bool, cohnP * (yw ν * xw ν) * cohnP = cohnP
  | [] => by rw [yw_nil, xw_nil, mul_one, mul_one, cohnP_mul_self]
  | i :: ν => by
    rw [yw_cons, xw_cons, yx_assoc, cy_cx_self, mul_one, cohnP_yx_cohnP_self ν]

theorem cohnP_yx_cohnP_ne :
    ∀ ν α : List Bool, ν ≠ α → cohnP * (yw ν * xw α) * cohnP = 0
  | [], [], h => (h rfl).elim
  | [], _ :: _, _ => by
    rw [yw_nil, xw_cons, one_mul, ← mul_assoc, cohnP_cx, zero_mul, zero_mul]
  | _ :: _, [], _ => by
    rw [yw_cons, xw_nil, mul_one, mul_assoc, mul_assoc, cy_cohnP, mul_zero, mul_zero]
  | i :: ν, j :: α, h => by
    by_cases hij : i = j
    · subst hij
      have hne : ν ≠ α := fun e => h (congrArg (List.cons i) e)
      rw [yw_cons, xw_cons, yx_assoc, cy_cx_self, mul_one, cohnP_yx_cohnP_ne ν α hne]
    · rw [yw_cons, xw_cons, yx_assoc, cy_cx_ne hij, mul_zero, zero_mul, mul_zero, zero_mul]

/-- The matrix unit law `e_{μν} e_{αβ} = δ_{να} e_{μβ}`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem unitE_mul_unitE (μ ν α β : List Bool) :
    unitE μ ν * unitE α β = if ν = α then unitE μ β else 0 := by
  have h : unitE μ ν * unitE α β = xw μ * (cohnP * (yw ν * xw α) * cohnP) * yw β := by
    simp only [unitE_def, mul_assoc]
  rw [h]
  by_cases hνα : ν = α
  · rw [if_pos hνα, ← hνα, cohnP_yx_cohnP_self, unitE_def]
  · rw [if_neg hνα, cohnP_yx_cohnP_ne ν α hνα, mul_zero, zero_mul]

theorem unitE_nil_nil : unitE [] [] = cohnP := by
  rw [unitE_def, xw_nil, yw_nil, one_mul, mul_one]

theorem cx_mul_unitE (i : Bool) (μ ν : List Bool) : cx i * unitE μ ν = unitE (i :: μ) ν := by
  rw [unitE_def, unitE_def, xw_cons]
  simp only [mul_assoc]

theorem unitE_mul_cy (i : Bool) (μ ν : List Bool) : unitE μ ν * cy i = unitE μ (i :: ν) := by
  rw [unitE_def, unitE_def, yw_cons, mul_assoc]

theorem cy_mul_unitE_nil (i : Bool) (ν : List Bool) : cy i * unitE [] ν = 0 := by
  rw [unitE_def, xw_nil, one_mul, ← mul_assoc, cy_cohnP, zero_mul]

theorem cy_mul_unitE_cons (i j : Bool) (μ ν : List Bool) :
    cy i * unitE (j :: μ) ν = cy i * cx j * unitE μ ν := by
  rw [unitE_def, unitE_def, xw_cons]
  simp only [mul_assoc]

theorem unitE_nil_mul_cx (i : Bool) (μ : List Bool) : unitE μ [] * cx i = 0 := by
  rw [unitE_def, yw_nil, mul_one, mul_assoc, cohnP_cx, mul_zero]

theorem unitE_cons_mul_cx (i j : Bool) (μ ν : List Bool) :
    unitE μ (j :: ν) * cx i = unitE μ ν * (cy j * cx i) := by
  rw [unitE_def, unitE_def, yw_cons]
  simp only [mul_assoc]

theorem toLeavitt_cx_false :
    toLeavitt (cx false) = BinaryLeavitt.quotientMap (ZMod 2)
      (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s0) :=
  toLeavitt_mk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s0)

theorem toLeavitt_cx_true :
    toLeavitt (cx true) = BinaryLeavitt.quotientMap (ZMod 2)
      (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s1) :=
  toLeavitt_mk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s1)

theorem toLeavitt_cy_false :
    toLeavitt (cy false) = BinaryLeavitt.quotientMap (ZMod 2)
      (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t0) :=
  toLeavitt_mk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t0)

theorem toLeavitt_cy_true :
    toLeavitt (cy true) = BinaryLeavitt.quotientMap (ZMod 2)
      (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t1) :=
  toLeavitt_mk (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t1)

/-- `p` dies in the Leavitt algebra (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem toLeavitt_cohnP : toLeavitt cohnP = 0 := by
  have h := RingQuot.mkAlgHom_rel (ZMod 2)
    (BinaryLeavitt.Relation.sum_range (k := ZMod 2))
  rw [map_add, map_mul, map_mul, map_one] at h
  have h' : BinaryLeavitt.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s0) *
        BinaryLeavitt.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t0) +
      BinaryLeavitt.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s1) *
        BinaryLeavitt.quotientMap (ZMod 2) (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t1) = 1 := h
  rw [cohnP_def, map_sub, map_sub, map_one, map_mul, map_mul, toLeavitt_cx_false,
    toLeavitt_cx_true, toLeavitt_cy_false, toLeavitt_cy_true, sub_sub, sub_eq_zero]
  exact h'.symm

theorem toLeavitt_unitE (μ ν : List Bool) : toLeavitt (unitE μ ν) = 0 := by
  rw [unitE_def, map_mul, map_mul, toLeavitt_cohnP, mul_zero, zero_mul]

theorem toLeavitt_smul_unitE (c : ZMod 2) (μ ν : List Bool) :
    toLeavitt (c • unitE μ ν) = 0 := by
  rw [toLeavitt_smul, toLeavitt_unitE, smul_zero]

end

end GroupApproximation.Full.LVCohnRelK1
