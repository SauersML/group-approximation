import GroupApproximation.Leavitt.HilbertHotelSaturation
import GroupApproximation.Leavitt.Whitehead

/-!
# Ellipticity of the Hilbert-hotel stable letter

The Whitehead matrix `T = diag(U, U⁻¹)` of the `4m = 16` frame is *elliptic*: it
is a product of elementary transvections, so it lies in `E₁₆(R)` rather than
merely in `GL₁₆(R)`.  This is what lets the cover presentation downstream read
the stable letter `τ` off as a concrete word in the elementary generators.

The factorisation is Whitehead's, in the rank-two frame over the `2m = 8` block
ring: `W(Z) = x₁₂(Z)·x₂₁(-Z⁻¹)·x₁₂(Z)` and `W(Z)·W(-1) = diag(Z, Z⁻¹)`, giving
the explicit six-factor word

`T = x₁₂(U)·x₂₁(-V)·x₁₂(U)·x₁₂(-1)·x₂₁(1)·x₁₂(-1)`

(in characteristic two the three signs are free).  Flattening each block
transvection entry by entry lands the word in the ordinary elementary group of
the `16` frame.
-/

namespace GroupApproximation
namespace HilbertHotel

variable {R : Type*} [Ring R]

/-! ### The rank-two Whitehead word over an arbitrary ring -/

section RankTwo

variable {A : Type*} [Ring A]

theorem x12_eq_one_add_single (Z : A) :
    Whitehead.x12 Z = (1 : Matrix (Fin 2) (Fin 2) A) + Matrix.single 0 1 Z := by
  unfold Whitehead.x12
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem x21_eq_one_add_single (Z : A) :
    Whitehead.x21 Z = (1 : Matrix (Fin 2) (Fin 2) A) + Matrix.single 1 0 Z := by
  unfold Whitehead.x21
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem inv_neg_one_units : (-1 : Aˣ)⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (by simp)

/-- `W(-1)` is a word in three transvections with unit coefficients. -/
theorem w_neg_one :
    Whitehead.w (-1 : Aˣ)
      = Whitehead.x12 (-1 : A) * Whitehead.x21 (1 : A) * Whitehead.x12 (-1 : A) := by
  unfold Whitehead.w
  rw [inv_neg_one_units, Units.val_neg, Units.val_one, neg_neg]

end RankTwo

/-! ### The six-factor word for `T` -/

section Factors

variable (L : LeavittFamily R)

/-- The Whitehead matrix as a unit of the block frame. -/
def T16unit :
    (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)))ˣ where
  val := T16 L
  inv := T16inv L
  val_inv := T16_mul_T16inv L
  inv_val := T16inv_mul_T16 L

@[simp] theorem T16unit_val :
    (T16unit L : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)))
      = T16 L := rfl

theorem T16_eq_whitehead :
    T16 L = Whitehead.w (U8unit L) * Whitehead.w (-1) := by
  rw [← Whitehead.whitehead_diagonal (U8unit L)]
  rfl

/-- **The explicit Whitehead word.**  `T = diag(U, U⁻¹)` is the product of six
elementary block transvections of the rank-two frame over `M₈(R)`. -/
theorem T16_eq_six_transvections :
    T16 L = Whitehead.x12 (U8 L) * Whitehead.x21 (-(V8 L)) * Whitehead.x12 (U8 L)
      * Whitehead.x12 (-1) * Whitehead.x21 1 * Whitehead.x12 (-1) := by
  rw [T16_eq_whitehead, w_neg_one]
  unfold Whitehead.w
  simp only [U8unit_val, U8unit_inv_val, ← mul_assoc]

/-- The same word with the factors named as elementary units, which is the form
the cover presentation consumes: `τ` is the product of this six-letter list. -/
theorem T16unit_eq_six_elementary (h01 : (0 : Fin 2) ≠ 1) (h10 : (1 : Fin 2) ≠ 0) :
    T16unit L
      = elementaryUnit 0 1 h01 (U8 L) * elementaryUnit 1 0 h10 (-(V8 L))
        * elementaryUnit 0 1 h01 (U8 L) * elementaryUnit 0 1 h01 (-1)
        * elementaryUnit 1 0 h10 1 * elementaryUnit 0 1 h01 (-1) := by
  apply Units.ext
  show T16 L
    = ((1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)))
        + Matrix.single 0 1 (U8 L)) * (1 + Matrix.single 1 0 (-(V8 L)))
      * (1 + Matrix.single 0 1 (U8 L)) * (1 + Matrix.single 0 1 (-1))
      * (1 + Matrix.single 1 0 1) * (1 + Matrix.single 0 1 (-1))
  rw [T16_eq_six_transvections]
  simp only [x12_eq_one_add_single, x21_eq_one_add_single]

/-- The six-letter factor list itself. -/
def whiteheadFactors (h01 : (0 : Fin 2) ≠ 1) (h10 : (1 : Fin 2) ≠ 0) :
    List ((Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)))ˣ) :=
  [elementaryUnit 0 1 h01 (U8 L), elementaryUnit 1 0 h10 (-(V8 L)),
    elementaryUnit 0 1 h01 (U8 L), elementaryUnit 0 1 h01 (-1),
    elementaryUnit 1 0 h10 1, elementaryUnit 0 1 h01 (-1)]

theorem whiteheadFactors_prod (h01 : (0 : Fin 2) ≠ 1) (h10 : (1 : Fin 2) ≠ 0) :
    (whiteheadFactors L h01 h10).prod = T16unit L := by
  rw [T16unit_eq_six_elementary L h01 h10, whiteheadFactors]
  simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]

theorem whiteheadFactors_elementary (h01 : (0 : Fin 2) ≠ 1) (h10 : (1 : Fin 2) ≠ 0) :
    ∀ z ∈ whiteheadFactors L h01 h10,
      ∃ (i j : Fin 2) (h : i ≠ j)
        (a : Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)),
        elementaryUnit i j h a = z := by
  intro z hz
  rw [whiteheadFactors] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, h01, U8 L, rfl⟩
  · exact ⟨1, 0, h10, -(V8 L), rfl⟩
  · exact ⟨0, 1, h01, U8 L, rfl⟩
  · exact ⟨0, 1, h01, -1, rfl⟩
  · exact ⟨1, 0, h10, 1, rfl⟩
  · exact ⟨0, 1, h01, -1, rfl⟩

end Factors

/-! ### Flattening the word into `E₁₆(R)` -/

section Flatten

/-- The block frame and the `16` frame have isomorphic unit groups. -/
def flat16Units (R : Type*) [Ring R] :
    (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)))ˣ ≃*
      (Matrix (Fin 16) (Fin 16) R)ˣ :=
  Units.mapEquiv (flat16 R).toMulEquiv

@[simp] theorem flat16Units_val
    (u : (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)))ˣ) :
    (flat16Units R u : Matrix (Fin 16) (Fin 16) R)
      = flat16 R (u : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R))) :=
  rfl

theorem flat16Units_elementary_single_mem (b c b' c' : Fin 2) (hbc : b ≠ c)
    (W : Matrix (Fin 4) (Fin 4) R) :
    flat16Units R (elementaryUnit b c hbc (Matrix.single b' c' W))
      ∈ elementaryGroup (Fin 16) R := by
  induction W using Matrix.induction_on' with
  | h_zero =>
      rw [Matrix.single_zero, elementaryUnit_zero, map_one]
      exact one_mem _
  | h_add M N hM hN =>
      rw [Matrix.single_add, ← elementaryUnit_mul, map_mul]
      exact mul_mem hM hN
  | h_std_basis i j x =>
      have hne : frame16 (b, (b', i)) ≠ frame16 (c, (c', j)) := by
        intro hcon
        exact hbc (congrArg (fun p => p.1) (frame16.injective hcon))
      have hval :
          flat16Units R (elementaryUnit b c hbc (Matrix.single b' c' (Matrix.single i j x)))
            = elementaryUnit (frame16 (b, (b', i))) (frame16 (c, (c', j))) hne x := by
        apply Units.ext
        show flat16 R ((1 : Matrix (Fin 2) (Fin 2)
            (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)))
              + Matrix.single b c (Matrix.single b' c' (Matrix.single i j x)))
          = 1 + Matrix.single (frame16 (b, (b', i))) (frame16 (c, (c', j))) x
        rw [map_add, map_one, flat16_single]
      rw [hval]
      exact elementaryUnit_mem _ _ _ _

theorem flat16Units_elementary_mem (b c : Fin 2) (hbc : b ≠ c)
    (Z : Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R)) :
    flat16Units R (elementaryUnit b c hbc Z) ∈ elementaryGroup (Fin 16) R := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
      rw [elementaryUnit_zero, map_one]
      exact one_mem _
  | h_add M N hM hN =>
      rw [← elementaryUnit_mul, map_mul]
      exact mul_mem hM hN
  | h_std_basis b' c' W => exact flat16Units_elementary_single_mem b c b' c' hbc W

variable (L : LeavittFamily R)

theorem Tunit_eq_flat16Units : Tunit L = flat16Units R (T16unit L) := by
  apply Units.ext
  rfl

/-- **Ellipticity.**  The Hilbert-hotel stable letter lies in the elementary
group of the `4m = 16` frame, not merely in `GL₁₆(R)`. -/
theorem Tunit_mem_elementaryGroup : Tunit L ∈ elementaryGroup (Fin 16) R := by
  rw [Tunit_eq_flat16Units, T16unit_eq_six_elementary L (by decide) (by decide)]
  simp only [map_mul]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (flat16Units_elementary_mem 0 1 (by decide) (U8 L))
    (flat16Units_elementary_mem 1 0 (by decide) (-(V8 L))))
    (flat16Units_elementary_mem 0 1 (by decide) (U8 L)))
    (flat16Units_elementary_mem 0 1 (by decide) (-1)))
    (flat16Units_elementary_mem 1 0 (by decide) 1))
    (flat16Units_elementary_mem 0 1 (by decide) (-1))

end Flatten

end HilbertHotel
end GroupApproximation
