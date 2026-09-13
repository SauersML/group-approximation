import GroupApproximation.KirchbergLoops.GraphRows

/-!
# Phasing one edge of `E(u)`: identity (4)

The STW Problem L artifact (`research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`, §2)
defines the automorphism `g_{ij,z}` of `C*(E(u))` for `z ∈ 𝕋`: it multiplies the edge
`a = a_ij^(1)` by `z` and fixes every other generator. Identity (4) says
`g_{ij,z}(W_k) W_k* = 1 + (z - 1) a a*` if `k = i`, and `1` otherwise.

This file proves (4) for any Cuntz–Krieger family of `E(u)` in a star ring, with `z` a central
unitary (for a unital ℂ-algebra, `z • 1` with `|z| = 1`). It does not build the universal algebra,
so it does not produce the automorphism `g_{ij,z}` itself. It builds the phased family, which is the
image of the generators under `g_{ij,z}`.

* `CuntzKriegerFamily.edgePhase`: the phased family is again a Cuntz–Krieger family.
* `CuntzKriegerFamily.edgePhase_W_of_ne`: `W_{k m}` is unchanged when `k, m ≠ i`.
* `CuntzKriegerFamily.edgePhase_W_mul_star_W`: identity (4), `W'_{i m} W_{i m}* = 1 + (z - 1) a a*`.
-/

namespace GroupApproximation
namespace KirchbergLoops

open Finset

variable {R : Type*} [Ring R] [StarRing R]

/-- The phase `z` on the edge `(i₀, e₀)` and `1` on every other edge. -/
def phaseCoeff (z : R) {n : ℕ} {u : Fin n → ℕ} (i₀ : Fin n) (e₀ : ArrowIndex u) (i : Fin n)
    (e : ArrowIndex u) : R :=
  if i = i₀ ∧ e = e₀ then z else 1

section Phase

variable {n : ℕ} {u : Fin n → ℕ} {z : R} {i₀ : Fin n} {e₀ : ArrowIndex u}

omit [StarRing R] in
theorem phaseCoeff_comm (hzc : ∀ x, z * x = x * z) (i : Fin n) (e : ArrowIndex u) (x : R) :
    phaseCoeff z i₀ e₀ i e * x = x * phaseCoeff z i₀ e₀ i e := by
  by_cases h : i = i₀ ∧ e = e₀
  · rw [phaseCoeff, if_pos h]
    exact hzc x
  · rw [phaseCoeff, if_neg h, one_mul, mul_one]

theorem star_phaseCoeff_comm (hzc : ∀ x, z * x = x * z) (i : Fin n) (e : ArrowIndex u) (x : R) :
    star (phaseCoeff z i₀ e₀ i e) * x = x * star (phaseCoeff z i₀ e₀ i e) := by
  have h := congrArg star (phaseCoeff_comm (i₀ := i₀) (e₀ := e₀) hzc i e (star x))
  rw [star_mul, star_mul, star_star] at h
  exact h.symm

theorem star_phaseCoeff_mul_self (hz : z ∈ unitary R) (i : Fin n) (e : ArrowIndex u) :
    star (phaseCoeff z i₀ e₀ i e) * phaseCoeff z i₀ e₀ i e = 1 := by
  by_cases h : i = i₀ ∧ e = e₀
  · rw [phaseCoeff, if_pos h]
    exact Unitary.star_mul_self_of_mem hz
  · rw [phaseCoeff, if_neg h, star_one, one_mul]

theorem phaseCoeff_mul_star_self (hz : z ∈ unitary R) (i : Fin n) (e : ArrowIndex u) :
    phaseCoeff z i₀ e₀ i e * star (phaseCoeff z i₀ e₀ i e) = 1 := by
  by_cases h : i = i₀ ∧ e = e₀
  · rw [phaseCoeff, if_pos h]
    exact Unitary.mul_star_self_of_mem hz
  · rw [phaseCoeff, if_neg h, star_one, one_mul]

end Phase

theorem star_mul_mul_of_comm {w₁ w₂ x y : R} (h₁ : ∀ r, star w₁ * r = r * star w₁)
    (h₂ : ∀ r, w₂ * r = r * w₂) :
    star (w₁ * x) * (w₂ * y) = star w₁ * w₂ * (star x * y) := by
  have hc : ∀ r, star w₁ * w₂ * r = r * (star w₁ * w₂) := fun r => by
    rw [mul_assoc (star w₁) w₂ r, h₂ r, ← mul_assoc (star w₁) r w₂, h₁ r,
      mul_assoc r (star w₁) w₂]
  rw [star_mul, mul_assoc (star x) (star w₁) (w₂ * y), ← mul_assoc (star w₁) w₂ y, hc y,
    ← mul_assoc (star x) y (star w₁ * w₂), ← hc (star x * y)]

theorem mul_star_mul_of_comm {w x : R} (h : ∀ r, w * r = r * w) (hw : w * star w = 1) :
    w * x * star (w * x) = x * star x := by
  rw [star_mul, mul_assoc w x (star x * star w), ← mul_assoc x (star x) (star w),
    ← mul_assoc w (x * star x) (star w), h (x * star x), mul_assoc (x * star x) w (star w), hw,
    mul_one]

namespace CuntzKriegerFamily

variable {n : ℕ} {u : Fin n → ℕ} (F : CuntzKriegerFamily R n u)

/-- The edges multiplied by the phase `z` on `(i₀, e₀)`. -/
def phasedEdge (z : R) (i₀ : Fin n) (e₀ : ArrowIndex u) (i : Fin n) (e : ArrowIndex u) : R :=
  phaseCoeff z i₀ e₀ i e * F.a i e

/-- **The edge-phase family**, the image of the generators under `g_{ij,z}`. -/
def edgePhase {z : R} (hz : z ∈ unitary R) (hzc : ∀ x, z * x = x * z) (i₀ : Fin n)
    (e₀ : ArrowIndex u) : CuntzKriegerFamily R n u where
  p := F.p
  d := F.d
  a := F.phasedEdge z i₀ e₀
  star_d_mul_d := F.star_d_mul_d
  star_d_mul_a i i' e := by
    simp only [phasedEdge]
    rw [phaseCoeff_comm hzc i' e (F.a i' e), ← mul_assoc, F.star_d_mul_a, zero_mul]
  star_a_mul_a i e i' e' := by
    simp only [phasedEdge]
    rw [star_mul_mul_of_comm (star_phaseCoeff_comm hzc i e) (phaseCoeff_comm hzc i' e'),
      F.star_a_mul_a]
    by_cases h : i = i' ∧ e = e'
    · rw [if_pos h, h.1, h.2, star_phaseCoeff_mul_self hz, one_mul]
    · rw [if_neg h, mul_zero]
  sum_source i := by
    have h : ∀ e, phaseCoeff z i₀ e₀ i e * F.a i e * star (phaseCoeff z i₀ e₀ i e * F.a i e) =
        F.a i e * star (F.a i e) := fun e =>
      mul_star_mul_of_comm (phaseCoeff_comm hzc i e) (phaseCoeff_mul_star_self hz i e)
    simp only [phasedEdge, h]
    exact F.sum_source i
  sum_p := F.sum_p

variable {z : R} (hz : z ∈ unitary R) (hzc : ∀ x, z * x = x * z) (i₀ : Fin n) (e₀ : ArrowIndex u)

theorem edgePhase_a (i : Fin n) (e : ArrowIndex u) :
    (F.edgePhase hz hzc i₀ e₀).a i e = phaseCoeff z i₀ e₀ i e * F.a i e := rfl

theorem edgePhase_row_inl (i j : Fin n) :
    (F.edgePhase hz hzc i₀ e₀).row i (.inl j) = F.row i (.inl j) := rfl

theorem edgePhase_row_of_ne {i : Fin n} (h : i ≠ i₀) (c : RowIndex u) :
    (F.edgePhase hz hzc i₀ e₀).row i c = F.row i c := by
  rcases c with j | e
  · exact F.edgePhase_row_inl hz hzc i₀ e₀ i j
  · have hne : ¬(i = i₀ ∧ e = e₀) := fun h' => h h'.1
    simp only [row_inr, edgePhase_a]
    rw [phaseCoeff, if_neg hne, one_mul]

theorem edgePhase_row_self (c : RowIndex u) :
    (F.edgePhase hz hzc i₀ e₀).row i₀ c =
      F.row i₀ c + if c = .inr e₀ then (z - 1) * F.a i₀ e₀ else 0 := by
  rcases c with j | e
  · have hc : (Sum.inl j : RowIndex u) ≠ Sum.inr e₀ := Sum.inl_ne_inr
    rw [if_neg hc, add_zero]
    exact F.edgePhase_row_inl hz hzc i₀ e₀ i₀ j
  · simp only [row_inr, edgePhase_a]
    by_cases he : e = e₀
    · have hc : (Sum.inr e : RowIndex u) = Sum.inr e₀ := congrArg Sum.inr he
      rw [if_pos hc, phaseCoeff, if_pos (And.intro rfl he), he, sub_mul, one_mul]
      abel
    · have hc : (Sum.inr e : RowIndex u) ≠ Sum.inr e₀ := fun h => he (Sum.inr_injective h)
      have hne : ¬(i₀ = i₀ ∧ e = e₀) := fun h => he h.2
      rw [if_neg hc, phaseCoeff, if_neg hne, one_mul, add_zero]

/-- **`W_{k m}` is fixed by `g_{ij,z}` when `k, m ≠ i`.** -/
theorem edgePhase_W_of_ne {k m : Fin n} (hk : k ≠ i₀) (hm : m ≠ i₀) :
    (F.edgePhase hz hzc i₀ e₀).W k m = F.W k m := by
  simp only [W, F.edgePhase_row_of_ne hz hzc i₀ e₀ hk, F.edgePhase_row_of_ne hz hzc i₀ e₀ hm]

/-- **Identity (4).** With `W'` the rows of the phased family, `W'_{i m} W_{i m}* = 1 + (z - 1) a a*`
for `a = a i e₀` and `m ≠ i`. -/
theorem edgePhase_W_mul_star_W {m : Fin n} (hm : m ≠ i₀) :
    (F.edgePhase hz hzc i₀ e₀).W i₀ m * star (F.W i₀ m) =
      1 + (z - 1) * (F.a i₀ e₀ * star (F.a i₀ e₀)) := by
  have hW : (F.edgePhase hz hzc i₀ e₀).W i₀ m =
      ∑ c, (F.edgePhase hz hzc i₀ e₀).row i₀ c * star (F.row m c) := by
    simp only [W, F.edgePhase_row_of_ne hz hzc i₀ e₀ hm]
  have hs : star (F.W i₀ m) = ∑ c, F.row m c * star (F.row i₀ c) := by
    simp only [W, star_sum, star_mul, star_star]
  have hx : ∀ c, (F.edgePhase hz hzc i₀ e₀).row i₀ c * F.rowProj c =
      (F.edgePhase hz hzc i₀ e₀).row i₀ c :=
    mul_rowProj_of_row ((F.edgePhase hz hzc i₀ e₀).sum_row_mul_star_row i₀)
      ((F.edgePhase hz hzc i₀ e₀).star_row_mul_row i₀)
  rw [hW, hs, sum_mul_star_mul_sum hx (F.star_row_mul_row m)]
  simp only [F.edgePhase_row_self hz hzc i₀ e₀, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, F.sum_row_mul_star_row i₀, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ (Sum.inr e₀ : RowIndex u)), row_inr, mul_assoc (z - 1)]

end CuntzKriegerFamily

end KirchbergLoops
end GroupApproximation
