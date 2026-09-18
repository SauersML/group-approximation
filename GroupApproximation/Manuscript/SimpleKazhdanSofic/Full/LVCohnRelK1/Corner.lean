import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic.NoncommRing

/-!
# Lifting matrices along a system of matrix units

Let `A` be an algebra over a field `𝕜` with a finite family of matrix units `e_{ab}`
(`e_{ab} e_{cd} = δ_{bc} e_{ad}`).  The map `B ↦ 1 + ∑ (B - 1)_{ab} e_{ab}` is multiplicative, and
it sends transvections to elementary elements `1 + c e_{ab}`.  Over `𝔽₂` a matrix whose image has a
left inverse maps to a product of such elementary elements (row reduction plus the fact that the
diagonal part lifts to `1`).  This is the excision step for the ideal `M_∞(𝔽₂)` of the Cohn
algebra in step W1 of `simple_kazhdan_sofic_group.tex` l.733-735.
-/

namespace GroupApproximation.Full.LVCohnRelK1

open Matrix

section Corner

variable {𝕜 A κ : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] [Fintype κ] [DecidableEq κ]

/-- `∑_{a,b} B_{ab} e_{ab}` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
def unitSum (E : κ → κ → A) (B : Matrix κ κ 𝕜) : A := ∑ a, ∑ b, B a b • E a b

/-- `1 + ∑_{a,b} (B - 1)_{ab} e_{ab}` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
def unitLift (E : κ → κ → A) (B : Matrix κ κ 𝕜) : A := 1 + unitSum E (B - 1)

theorem unitSum_zero (E : κ → κ → A) : unitSum E (0 : Matrix κ κ 𝕜) = 0 := by
  simp only [unitSum, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

theorem unitSum_add (E : κ → κ → A) (B B' : Matrix κ κ 𝕜) :
    unitSum E (B + B') = unitSum E B + unitSum E B' := by
  simp only [unitSum, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem unitLift_one (E : κ → κ → A) : unitLift E (1 : Matrix κ κ 𝕜) = 1 := by
  change 1 + unitSum E ((1 : Matrix κ κ 𝕜) - 1) = 1
  rw [sub_self, unitSum_zero, add_zero]

theorem smul_unit_mul_unitSum {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (B B' : Matrix κ κ 𝕜) (a b : κ) :
    (B a b • E a b) * unitSum E B' = ∑ d, (B a b * B' b d) • E a d := by
  have h0 : ∀ c, c ≠ b → (B a b • E a b) * ∑ d, B' c d • E c d = 0 := fun c hc => by
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [smul_mul_smul_comm, hE, if_neg (Ne.symm hc), smul_zero]
  have h1 : (B a b • E a b) * ∑ d, B' b d • E b d = ∑ d, (B a b * B' b d) • E a d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_mul_smul_comm, hE, if_pos rfl]
  calc (B a b • E a b) * unitSum E B'
      = ∑ c, (B a b • E a b) * ∑ d, B' c d • E c d := by
        change (B a b • E a b) * ∑ c, ∑ d, B' c d • E c d = _
        exact Finset.mul_sum _ _ _
    _ = (B a b • E a b) * ∑ d, B' b d • E b d :=
      Finset.sum_eq_single_of_mem b (Finset.mem_univ b) fun c _ hc => h0 c hc
    _ = ∑ d, (B a b * B' b d) • E a d := h1

/-- The lift of matrices is multiplicative on the non-unital part
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem unitSum_mul {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (B B' : Matrix κ κ 𝕜) : unitSum E B * unitSum E B' = unitSum E (B * B') := by
  have h1 : unitSum E B * unitSum E B' = ∑ a, ∑ b, (B a b • E a b) * unitSum E B' := by
    change (∑ a, ∑ b, B a b • E a b) * unitSum E B' = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_mul _ _ _
  have h2 : ∀ a d, ∑ b, (B a b * B' b d) • E a d = (B * B') a d • E a d := fun a d => by
    rw [Matrix.mul_apply, Finset.sum_smul]
  calc unitSum E B * unitSum E B'
      = ∑ a, ∑ b, ∑ d, (B a b * B' b d) • E a d := by
        rw [h1]
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => smul_unit_mul_unitSum hE B B' a b
    _ = ∑ a, ∑ d, ∑ b, (B a b * B' b d) • E a d :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a, ∑ d, (B * B') a d • E a d :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => h2 a d
    _ = unitSum E (B * B') := rfl

theorem unitLift_mul {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (B B' : Matrix κ κ 𝕜) : unitLift E (B * B') = unitLift E B * unitLift E B' := by
  have h : B * B' - 1 = (B - 1) + (B' - 1) + (B - 1) * (B' - 1) := by noncomm_ring
  have hs := unitSum_mul hE (B - 1) (B' - 1)
  calc unitLift E (B * B') = 1 + unitSum E (B * B' - 1) := rfl
    _ = 1 + (unitSum E (B - 1) + unitSum E (B' - 1) +
          unitSum E (B - 1) * unitSum E (B' - 1)) := by
        rw [h, unitSum_add, unitSum_add, ← hs]
    _ = (1 + unitSum E (B - 1)) * (1 + unitSum E (B' - 1)) := by noncomm_ring
    _ = unitLift E B * unitLift E B' := rfl

theorem unitSum_single (E : κ → κ → A) (i j : κ) (c : 𝕜) :
    unitSum E (Matrix.single i j c) = c • E i j := by
  have h1 : ∀ a, a ≠ i → ∑ b, Matrix.single i j c a b • E a b = 0 := fun a ha =>
    Finset.sum_eq_zero fun b _ => by
      rw [Matrix.single_apply_of_row_ne (Ne.symm ha), zero_smul]
  have h2 : ∀ b, b ≠ j → Matrix.single i j c i b • E i b = 0 := fun b hb => by
    rw [Matrix.single_apply_of_col_ne i i (Ne.symm hb), zero_smul]
  calc unitSum E (Matrix.single i j c) = ∑ a, ∑ b, Matrix.single i j c a b • E a b := rfl
    _ = ∑ b, Matrix.single i j c i b • E i b :=
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun a _ ha => h1 a ha
    _ = Matrix.single i j c i j • E i j :=
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun b _ hb => h2 b hb
    _ = c • E i j := by rw [Matrix.single_apply_same]

/-- Transvections lift to elementary elements `1 + c e_{ij}`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem unitLift_toMatrix (E : κ → κ → A) (t : TransvectionStruct κ 𝕜) :
    unitLift E t.toMatrix = 1 + t.c • E t.i t.j := by
  change 1 + unitSum E ((1 + Matrix.single t.i t.j t.c) - 1) = _
  rw [add_sub_cancel_left, unitSum_single]

theorem unitLift_transvec_prod {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0) :
    ∀ L : List (TransvectionStruct κ 𝕜),
      unitLift E (L.map TransvectionStruct.toMatrix).prod =
        (L.map fun t => 1 + t.c • E t.i t.j).prod
  | [] => by simp only [List.map_nil, List.prod_nil, unitLift_one]
  | t :: L => by
    simp only [List.map_cons, List.prod_cons]
    rw [unitLift_mul hE, unitLift_transvec_prod hE L, unitLift_toMatrix]

theorem unitSum_mul_unit {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (B : Matrix κ κ 𝕜) (c d : κ) : unitSum E B * E c d = ∑ a, B a c • E a d := by
  have h0 : ∀ a b, b ≠ c → B a b • E a b * E c d = 0 := fun a b hb => by
    rw [smul_mul_assoc, hE, if_neg hb, smul_zero]
  have h1 : ∀ a, ∑ b, B a b • E a b * E c d = B a c • E a d := fun a => by
    calc ∑ b, B a b • E a b * E c d = B a c • E a c * E c d :=
          Finset.sum_eq_single_of_mem c (Finset.mem_univ c) fun b _ hb => h0 a b hb
      _ = B a c • E a d := by rw [smul_mul_assoc, hE, if_pos rfl]
  calc unitSum E B * E c d = ∑ a, ∑ b, B a b • E a b * E c d := by
        change (∑ a, ∑ b, B a b • E a b) * E c d = _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_mul _ _ _
    _ = ∑ a, B a c • E a d := Finset.sum_congr rfl fun a _ => h1 a

/-- Over a field in which every element is `0` or `1` (that is, `𝔽₂`), a diagonal matrix whose
lift has a left inverse lifts to `1` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem unitLift_diagonal_eq_one {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (hD : ∀ x : 𝕜, x = 0 ∨ x = 1) (D : κ → 𝕜) {G : A}
    (hG : G * unitLift E (Matrix.diagonal D) = 1) : unitLift E (Matrix.diagonal D) = 1 := by
  have hoff : ∀ a b, a ≠ b → (Matrix.diagonal D - 1) a b = 0 := fun a b hab => by
    rw [Matrix.sub_apply, Matrix.diagonal_apply_ne D hab, Matrix.one_apply_ne hab, sub_zero]
  have hon : ∀ a, (Matrix.diagonal D - 1) a a = D a - 1 := fun a => by
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
  have hcol : ∀ c, ∑ a, (Matrix.diagonal D - 1) a c • E a c = (D c - 1) • E c c := fun c => by
    calc ∑ a, (Matrix.diagonal D - 1) a c • E a c = (Matrix.diagonal D - 1) c c • E c c :=
          Finset.sum_eq_single_of_mem c (Finset.mem_univ c) fun a _ ha => by
            rw [hoff a c ha, zero_smul]
      _ = (D c - 1) • E c c := by rw [hon]
  have hzero : ∀ c, D c = 0 → E c c = 0 := fun c hc => by
    have hU : unitLift E (Matrix.diagonal D) * E c c = 0 := by
      calc unitLift E (Matrix.diagonal D) * E c c
          = E c c + unitSum E (Matrix.diagonal D - 1) * E c c := by
            change (1 + unitSum E (Matrix.diagonal D - 1)) * E c c = _
            rw [add_mul, one_mul]
        _ = 0 := by
            rw [unitSum_mul_unit hE, hcol, hc, zero_sub, neg_one_smul, add_neg_cancel]
    calc E c c = G * unitLift E (Matrix.diagonal D) * E c c := by rw [hG, one_mul]
      _ = 0 := by rw [mul_assoc, hU, mul_zero]
  have hterm : ∀ a b, (Matrix.diagonal D - 1) a b • E a b = 0 := fun a b => by
    by_cases hab : a = b
    · subst hab
      rw [hon]
      rcases hD (D a) with h | h
      · rw [hzero a h, smul_zero]
      · rw [h, sub_self, zero_smul]
    · rw [hoff a b hab, zero_smul]
  have hsum : unitSum E (Matrix.diagonal D - 1) = 0 := by
    change ∑ a, ∑ b, (Matrix.diagonal D - 1) a b • E a b = 0
    exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => hterm a b
  calc unitLift E (Matrix.diagonal D) = 1 + unitSum E (Matrix.diagonal D - 1) := rfl
    _ = 1 := by rw [hsum, add_zero]

/-- If `B = X D Y` and `Y` has a right inverse, then a left inverse of the lift of `B` gives a
left inverse of the lift of `D` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem unitLift_left_inv_conj {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    {B Dg X Y Yi : Matrix κ κ 𝕜} (hYi : Y * Yi = 1) (hB : B = X * Dg * Y) {G : A}
    (hG : G * unitLift E B = 1) :
    (unitLift E Y * G * unitLift E X) * unitLift E Dg = 1 := by
  have h1 : unitLift E X * unitLift E Dg = unitLift E B * unitLift E Yi := by
    rw [← unitLift_mul hE, ← unitLift_mul hE, hB, mul_assoc (X * Dg) Y Yi, hYi, mul_one]
  have h2 : unitLift E Y * unitLift E Yi = 1 := by
    rw [← unitLift_mul hE, hYi, unitLift_one]
  calc unitLift E Y * G * unitLift E X * unitLift E Dg
      = unitLift E Y * (G * unitLift E B) * unitLift E Yi := by
        simp only [mul_assoc, h1]
    _ = 1 := by rw [hG, mul_one, h2]

/-- **Corner lifting.**  Over `𝔽₂`, if the lift of `B` has a left inverse then it is a product of
elementary elements `1 + c e_{ij}` with `i ≠ j` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem unitLift_factor {E : κ → κ → A}
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (hD : ∀ x : 𝕜, x = 0 ∨ x = 1) (B : Matrix κ κ 𝕜) {G : A} (hG : G * unitLift E B = 1) :
    ∃ L : List (TransvectionStruct κ 𝕜),
      unitLift E B = (L.map fun t => 1 + t.c • E t.i t.j).prod := by
  obtain ⟨L, L', D, hB⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec B
  have hDg : unitLift E (Matrix.diagonal D) = 1 :=
    unitLift_diagonal_eq_one hE hD D
      (unitLift_left_inv_conj hE (TransvectionStruct.prod_mul_reverse_inv_prod L') hB hG)
  refine ⟨L ++ L', ?_⟩
  calc unitLift E B
      = unitLift E ((L.map TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
          (L'.map TransvectionStruct.toMatrix).prod) := congrArg (unitLift E) hB
    _ = unitLift E (L.map TransvectionStruct.toMatrix).prod * unitLift E (Matrix.diagonal D) *
          unitLift E (L'.map TransvectionStruct.toMatrix).prod := by
        rw [unitLift_mul hE, unitLift_mul hE]
    _ = unitLift E (L.map TransvectionStruct.toMatrix).prod *
          unitLift E (L'.map TransvectionStruct.toMatrix).prod := by
        rw [hDg, mul_one]
    _ = ((L ++ L').map fun t => 1 + t.c • E t.i t.j).prod := by
        rw [unitLift_transvec_prod hE, unitLift_transvec_prod hE, List.map_append,
          List.prod_append]

end Corner

end GroupApproximation.Full.LVCohnRelK1
