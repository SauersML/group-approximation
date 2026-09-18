import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.UpperTriangular
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Unitriangular `4 × 4` matrices and integral rounding

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform` (the Guentner--Higson--Weinberger property A step for
`Σ ≤ GL₄(ℚ)`): every element of `GL₄(ℚ)` is within bounded distance of a dyadic
grid point `diag(2^k) · m` of the Borel subgroup.  This file provides the
unipotent part of that approximation:

* `uni a b c d e f`, the unitriangular matrix with the six given entries above
  the diagonal, its multiplication law `uni_mul_uni` and its explicit inverse
  `uniInv`;
* integrality and entry bounds of unitriangular matrices;
* `uni_round`: every rational unitriangular matrix factors as `m · g` with `m`
  integral unitriangular and all parameters of `g` in `[0, 1)`.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExplicitLinearModel

/-- The unitriangular `4 × 4` matrix with upper entries `a b c / d e / f`. -/
def uni (a b c d e f : ℚ) : Mat :=
  !![1, a, b, c; 0, 1, d, e; 0, 0, 1, f; 0, 0, 0, 1]

theorem uni_congr {a b c d e f a' b' c' d' e' f' : ℚ} (h1 : a = a') (h2 : b = b')
    (h3 : c = c') (h4 : d = d') (h5 : e = e') (h6 : f = f') :
    uni a b c d e f = uni a' b' c' d' e' f' := by
  subst h1 h2 h3 h4 h5 h6
  rfl

theorem uni_zero : uni 0 0 0 0 0 0 = 1 :=
  Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | simp [uni]

/-- Multiplication law of unitriangular matrices. -/
theorem uni_mul_uni (a b c d e f a' b' c' d' e' f' : ℚ) :
    uni a b c d e f * uni a' b' c' d' e' f' =
      uni (a + a') (b + a * d' + b') (c + a * e' + b * f' + c') (d + d')
        (e + d * f' + e') (f + f') :=
  Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [uni, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The inverse of `uni a b c d e f`. -/
def uniInv (a b c d e f : ℚ) : Mat :=
  uni (-a) (-b + a * d) (-c + a * e + b * f - a * d * f) (-d) (-e + d * f) (-f)

theorem uni_mul_uniInv (a b c d e f : ℚ) : uni a b c d e f * uniInv a b c d e f = 1 := by
  rw [uniInv, uni_mul_uni, ← uni_zero]
  exact uni_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem uniInv_mul_uni (a b c d e f : ℚ) : uniInv a b c d e f * uni a b c d e f = 1 := by
  rw [uniInv, uni_mul_uni, ← uni_zero]
  exact uni_congr (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

theorem isUpperTri_uni (a b c d e f : ℚ) : IsUpperTri (uni a b c d e f) := by
  intro i j hji
  revert hji
  fin_cases i <;> fin_cases j <;>
    first
    | exact fun _ => rfl
    | exact fun h => absurd h (by decide)

theorem uni_apply_diag (a b c d e f : ℚ) (i : Fin 4) : uni a b c d e f i i = 1 := by
  fin_cases i <;> rfl

/-- A unitriangular matrix is determined by its six upper entries. -/
theorem eq_uni_of_unitriangular {V : Mat} (hup : IsUpperTri V) (hd : ∀ i, V i i = 1) :
    V = uni (V 0 1) (V 0 2) (V 0 3) (V 1 2) (V 1 3) (V 2 3) :=
  Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact hd _
      | exact hup _ _ (by decide)

/-- Integral parameters give an integral unitriangular matrix. -/
theorem isIntegral_uni {a b c d e f : ℚ} (ha : a ∈ (Int.castRingHom ℚ).range)
    (hb : b ∈ (Int.castRingHom ℚ).range) (hc : c ∈ (Int.castRingHom ℚ).range)
    (hd : d ∈ (Int.castRingHom ℚ).range) (he : e ∈ (Int.castRingHom ℚ).range)
    (hf : f ∈ (Int.castRingHom ℚ).range) : IsIntegral (uni a b c d e f) := by
  have h0 : (0 : ℚ) ∈ (Int.castRingHom ℚ).range := Subring.zero_mem _
  have h1 : (1 : ℚ) ∈ (Int.castRingHom ℚ).range := Subring.one_mem _
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
    | exact h0
    | exact h1
    | exact ha
    | exact hb
    | exact hc
    | exact hd
    | exact he
    | exact hf

/-- Entry bound for a unitriangular matrix with bounded parameters. -/
theorem abs_uni_apply_le {a b c d e f r : ℚ} (hr : 1 ≤ r) (ha : |a| ≤ r) (hb : |b| ≤ r)
    (hc : |c| ≤ r) (hd : |d| ≤ r) (he : |e| ≤ r) (hf : |f| ≤ r) (i j : Fin 4) :
    |uni a b c d e f i j| ≤ r := by
  have h0 : |(0 : ℚ)| ≤ r := by
    rw [abs_zero]
    linarith
  have h1 : |(1 : ℚ)| ≤ r := by
    rw [abs_one]
    exact hr
  fin_cases i <;> fin_cases j <;>
    first
    | exact h0
    | exact h1
    | exact ha
    | exact hb
    | exact hc
    | exact hd
    | exact he
    | exact hf

theorem intCast_mem_range (p : ℤ) : (p : ℚ) ∈ (Int.castRingHom ℚ).range :=
  ⟨p, rfl⟩

/-- The integral unitriangular unit with integer parameters. -/
def uniUnit (p B C q E r : ℤ) : Matˣ where
  val := uni p B C q E r
  inv := uniInv p B C q E r
  val_inv := uni_mul_uniInv _ _ _ _ _ _
  inv_val := uniInv_mul_uni _ _ _ _ _ _

theorem isIntegralUnitriangular_uniUnit (p B C q E r : ℤ) :
    IsIntegralUnitriangular (uniUnit p B C q E r) := by
  have hp := intCast_mem_range p
  have hB := intCast_mem_range B
  have hC := intCast_mem_range C
  have hq := intCast_mem_range q
  have hE := intCast_mem_range E
  have hr := intCast_mem_range r
  refine ⟨⟨?_, ?_⟩, isUpperTri_uni _ _ _ _ _ _, isUpperTri_uni _ _ _ _ _ _,
    fun i => ⟨uni_apply_diag _ _ _ _ _ _ i, uni_apply_diag _ _ _ _ _ _ i⟩⟩
  · exact isIntegral_uni hp hB hC hq hE hr
  · exact isIntegral_uni (Subring.neg_mem _ hp)
      (Subring.add_mem _ (Subring.neg_mem _ hB) (Subring.mul_mem _ hp hq))
      (Subring.sub_mem _
        (Subring.add_mem _ (Subring.add_mem _ (Subring.neg_mem _ hC) (Subring.mul_mem _ hp hE))
          (Subring.mul_mem _ hB hr))
        (Subring.mul_mem _ (Subring.mul_mem _ hp hq) hr))
      (Subring.neg_mem _ hq) (Subring.add_mem _ (Subring.neg_mem _ hE) (Subring.mul_mem _ hq hr))
      (Subring.neg_mem _ hr)

/-- Bounds for a unitriangular matrix with parameters in `[0, 1)` and for its
inverse. -/
theorem abs_uni_frac_le {a b c d e f : ℚ} (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1)
    (hc : 0 ≤ c ∧ c < 1) (hd : 0 ≤ d ∧ d < 1) (he : 0 ≤ e ∧ e < 1) (hf : 0 ≤ f ∧ f < 1)
    (i j : Fin 4) : |uni a b c d e f i j| ≤ 2 ∧ |uniInv a b c d e f i j| ≤ 2 := by
  have hr : (1 : ℚ) ≤ 2 := by norm_num
  have hs : ∀ x : ℚ, 0 ≤ x ∧ x < 1 → |x| ≤ 2 := fun x hx =>
    abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have had0 : 0 ≤ a * d := mul_nonneg ha.1 hd.1
  have had1 : a * d ≤ 1 := mul_le_one₀ ha.2.le hd.1 hd.2.le
  have hae0 : 0 ≤ a * e := mul_nonneg ha.1 he.1
  have hae1 : a * e ≤ 1 := mul_le_one₀ ha.2.le he.1 he.2.le
  have hbf0 : 0 ≤ b * f := mul_nonneg hb.1 hf.1
  have hbf1 : b * f ≤ 1 := mul_le_one₀ hb.2.le hf.1 hf.2.le
  have hdf0 : 0 ≤ d * f := mul_nonneg hd.1 hf.1
  have hdf1 : d * f ≤ 1 := mul_le_one₀ hd.2.le hf.1 hf.2.le
  have hadf0 : 0 ≤ a * d * f := mul_nonneg had0 hf.1
  have hadf1 : a * d * f ≤ 1 := mul_le_one₀ had1 hf.1 hf.2.le
  refine ⟨abs_uni_apply_le hr (hs a ha) (hs b hb) (hs c hc) (hs d hd) (hs e he) (hs f hf) i j,
    abs_uni_apply_le hr ?_ ?_ ?_ ?_ ?_ ?_ i j⟩
  · exact abs_le.mpr ⟨by linarith [ha.2], by linarith [ha.1]⟩
  · exact abs_le.mpr ⟨by linarith [hb.2], by linarith [hb.1]⟩
  · exact abs_le.mpr ⟨by linarith [hc.2], by linarith [hc.1]⟩
  · exact abs_le.mpr ⟨by linarith [hd.2], by linarith [hd.1]⟩
  · exact abs_le.mpr ⟨by linarith [he.2], by linarith [he.1]⟩
  · exact abs_le.mpr ⟨by linarith [hf.2], by linarith [hf.1]⟩

/-- **Integral rounding** of a unitriangular matrix: `uni a b c d e f = m · g`
with `m` integral unitriangular and the parameters of `g` in `[0, 1)`. -/
theorem uni_round (a b c d e f : ℚ) :
    ∃ p B C q E r : ℤ, ∃ a' b' c' d' e' f' : ℚ,
      uni a b c d e f = uni p B C q E r * uni a' b' c' d' e' f' ∧
      (0 ≤ a' ∧ a' < 1) ∧ (0 ≤ b' ∧ b' < 1) ∧ (0 ≤ c' ∧ c' < 1) ∧
      (0 ≤ d' ∧ d' < 1) ∧ (0 ≤ e' ∧ e' < 1) ∧ (0 ≤ f' ∧ f' < 1) := by
  have hA := Int.floor_add_fract a
  have hD := Int.floor_add_fract d
  have hF := Int.floor_add_fract f
  have hBx := Int.floor_add_fract (b - (⌊a⌋ : ℚ) * Int.fract d)
  have hEx := Int.floor_add_fract (e - (⌊d⌋ : ℚ) * Int.fract f)
  have hCx := Int.floor_add_fract (c - (⌊a⌋ : ℚ) * Int.fract (e - (⌊d⌋ : ℚ) * Int.fract f) -
    (⌊b - (⌊a⌋ : ℚ) * Int.fract d⌋ : ℚ) * Int.fract f)
  refine ⟨⌊a⌋, ⌊b - (⌊a⌋ : ℚ) * Int.fract d⌋,
    ⌊c - (⌊a⌋ : ℚ) * Int.fract (e - (⌊d⌋ : ℚ) * Int.fract f) -
      (⌊b - (⌊a⌋ : ℚ) * Int.fract d⌋ : ℚ) * Int.fract f⌋,
    ⌊d⌋, ⌊e - (⌊d⌋ : ℚ) * Int.fract f⌋, ⌊f⌋,
    Int.fract a, Int.fract (b - (⌊a⌋ : ℚ) * Int.fract d),
    Int.fract (c - (⌊a⌋ : ℚ) * Int.fract (e - (⌊d⌋ : ℚ) * Int.fract f) -
      (⌊b - (⌊a⌋ : ℚ) * Int.fract d⌋ : ℚ) * Int.fract f),
    Int.fract d, Int.fract (e - (⌊d⌋ : ℚ) * Int.fract f), Int.fract f, ?_,
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩⟩
  rw [uni_mul_uni]
  exact uni_congr (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)

end GroupApproximation.Full.NN09b
