import Mathlib.Algebra.Order.Field.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# The generators of Brown's `F_{n,∞}`

Hyde and Lodha use the Higman–Thompson group `F_n` through Brown's presentation
`F_n = ⟨x_0, x_1, … | x_i⁻¹ x_j x_i = x_{j+n-1}  (i < j)⟩` (right actions).  This module
builds the generators as permutations of `ℚ`, for `n = m + 2`, in Brown's model on the
half line: `x_k` is the identity on `(-∞, k]`, has slope `n` on `[k, k+1]`, and translates
by `n - 1` on `[k+1, ∞)`.

Permutations compose on the left here (`(f * g) t = f (g t)`), so Brown's relation reads
`x_i * x_j = x_{j+n-1} * x_i` for `i < j` (`xg_comm`), checked point by point.
The three displacement facts at the end (`x_k` fixes `(-∞, k]`, never moves a point
down, and has slope `n` just right of `k`) are what the normal-form injectivity
argument reads off.
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m : ℕ)

/-- The generator `x_k` of `F_{m+2,∞}` as a function on `ℚ`. -/
def xfun (k : ℕ) (t : ℚ) : ℚ :=
  if t ≤ k then t else if t ≤ k + 1 then k + ((m : ℚ) + 2) * (t - k) else t + ((m : ℚ) + 1)

variable {m}

theorem mTwo_pos : (0 : ℚ) < (m : ℚ) + 2 := by positivity

theorem xfun_of_le {k : ℕ} {t : ℚ} (h : t ≤ k) : xfun m k t = t := by
  simp [xfun, h]

theorem xfun_of_mem {k : ℕ} {t : ℚ} (h1 : (k : ℚ) ≤ t) (h2 : t ≤ k + 1) :
    xfun m k t = k + ((m : ℚ) + 2) * (t - k) := by
  unfold xfun
  split_ifs with ha hb
  · have ht : t = k := le_antisymm ha h1
    rw [ht]
    ring
  · rfl
  · exact absurd h2 hb

theorem xfun_of_ge {k : ℕ} {t : ℚ} (h : (k : ℚ) + 1 ≤ t) : xfun m k t = t + ((m : ℚ) + 1) := by
  unfold xfun
  split_ifs with ha hb
  · exfalso
    linarith
  · have ht : t = k + 1 := le_antisymm hb h
    rw [ht]
    ring
  · rfl

theorem xfun_strictMono (k : ℕ) : StrictMono (xfun m k) := by
  intro s t hst
  have hm : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := by positivity
  unfold xfun
  split_ifs <;> nlinarith

theorem xfun_surjective (k : ℕ) : Function.Surjective (xfun m k) := by
  intro y
  have hm : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  by_cases h1 : y ≤ k
  · exact ⟨y, xfun_of_le h1⟩
  · by_cases h2 : y ≤ k + ((m : ℚ) + 2)
    · refine ⟨k + (y - k) / ((m : ℚ) + 2), ?_⟩
      have hpos : 0 ≤ (y - k) / ((m : ℚ) + 2) :=
        div_nonneg (sub_nonneg.mpr (le_of_lt (not_le.mp h1))) hm.le
      have hle : (y - k) / ((m : ℚ) + 2) ≤ 1 := by
        rw [div_le_one hm]
        linarith
      rw [xfun_of_mem (by linarith) (by linarith)]
      have h3 : ((m : ℚ) + 2) * ((y - k) / ((m : ℚ) + 2)) = y - k := by
        field_simp
      have h4 : (k : ℚ) + (y - k) / ((m : ℚ) + 2) - k = (y - k) / ((m : ℚ) + 2) := by ring
      rw [h4, h3]
      ring
    · refine ⟨y - ((m : ℚ) + 1), ?_⟩
      rw [xfun_of_ge (by linarith)]
      ring

variable (m) in
/-- The generator `x_k` of `F_{m+2,∞}` as a permutation of `ℚ`. -/
noncomputable def xg (k : ℕ) : Equiv.Perm ℚ :=
  Equiv.ofBijective (xfun m k) ⟨(xfun_strictMono k).injective, xfun_surjective k⟩

@[simp] theorem xg_apply (k : ℕ) (t : ℚ) : xg m k t = xfun m k t := rfl

theorem xg_strictMono (k : ℕ) : StrictMono (xg m k) := xfun_strictMono k

/-- **Brown's relation**, for left composition: `x_i x_j = x_{j+n-1} x_i` for `i < j`. -/
theorem xg_comm {i j : ℕ} (hij : i < j) :
    xg m i * xg m j = xg m (j + m + 1) * xg m i := by
  have hij' : (i : ℚ) + 1 ≤ j := by
    have h : i + 1 ≤ j := hij
    exact_mod_cast h
  have hm : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := by positivity
  have hcast : ((j + m + 1 : ℕ) : ℚ) = (j : ℚ) + m + 1 := by push_cast; ring
  ext t
  simp only [Equiv.Perm.mul_apply, xg_apply]
  rcases le_or_lt t i with h1 | h1
  · rw [xfun_of_le (show t ≤ (j : ℚ) by linarith), xfun_of_le h1,
      xfun_of_le (show t ≤ ((j + m + 1 : ℕ) : ℚ) by rw [hcast]; linarith)]
  rcases le_or_lt t (i + 1) with h2 | h2
  · rw [xfun_of_le (show t ≤ (j : ℚ) by linarith), xfun_of_mem h1.le h2,
      xfun_of_le (show (i : ℚ) + ((m : ℚ) + 2) * (t - i) ≤ ((j + m + 1 : ℕ) : ℚ) by
        rw [hcast]; nlinarith)]
  rcases le_or_lt t j with h3 | h3
  · rw [xfun_of_le h3, xfun_of_ge h2.le,
      xfun_of_le (show t + ((m : ℚ) + 1) ≤ ((j + m + 1 : ℕ) : ℚ) by rw [hcast]; linarith)]
  rcases le_or_lt t (j + 1) with h4 | h4
  · rw [xfun_of_mem h3.le h4, xfun_of_ge (show (i : ℚ) + 1 ≤ j + ((m : ℚ) + 2) * (t - j) by
        nlinarith), xfun_of_ge (show (i : ℚ) + 1 ≤ t by linarith),
      xfun_of_mem (show ((j + m + 1 : ℕ) : ℚ) ≤ t + ((m : ℚ) + 1) by rw [hcast]; linarith)
        (show t + ((m : ℚ) + 1) ≤ ((j + m + 1 : ℕ) : ℚ) + 1 by rw [hcast]; linarith), hcast]
    ring
  · rw [xfun_of_ge h4.le, xfun_of_ge (show (i : ℚ) + 1 ≤ t + ((m : ℚ) + 1) by linarith),
      xfun_of_ge (show (i : ℚ) + 1 ≤ t by linarith),
      xfun_of_ge (show ((j + m + 1 : ℕ) : ℚ) + 1 ≤ t + ((m : ℚ) + 1) by rw [hcast]; linarith)]

/-! ## Displacement -/

/-- `x_k` fixes every point of `(-∞, k]`. -/
theorem xg_fix {k : ℕ} {t : ℚ} (h : t ≤ k) : xg m k t = t := xfun_of_le h

/-- `x_k` never moves a point down. -/
theorem le_xg (k : ℕ) (t : ℚ) : t ≤ xg m k t := by
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := by positivity
  rw [xg_apply]
  rcases le_or_lt t k with h1 | h1
  · rw [xfun_of_le h1]
  rcases le_or_lt t (k + 1) with h2 | h2
  · rw [xfun_of_mem h1.le h2]
    nlinarith
  · rw [xfun_of_ge h2.le]
    linarith

/-- `x_k` has slope `m + 2` just right of `k`. -/
theorem xg_near {k : ℕ} {δ : ℚ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    xg m k (k + δ) = k + ((m : ℚ) + 2) * δ := by
  rw [xg_apply, xfun_of_mem (by linarith) (by linarith)]
  ring

/-- `x_k` moves every point of `(k, k+1]` strictly up. -/
theorem lt_xg_of_mem {k : ℕ} {t : ℚ} (h1 : (k : ℚ) < t) : t < xg m k t := by
  have hm : (0 : ℚ) < (m : ℚ) + 2 := mTwo_pos
  have hm0 : (0 : ℚ) ≤ (m : ℚ) := by positivity
  rw [xg_apply]
  rcases le_or_lt t (k + 1) with h2 | h2
  · rw [xfun_of_mem h1.le h2]
    nlinarith
  · rw [xfun_of_ge h2.le]
    linarith

#audit_axioms GroupApproximation.HigmanThompson.xg_comm
#audit_axioms GroupApproximation.HigmanThompson.le_xg

end HigmanThompson
end GroupApproximation
