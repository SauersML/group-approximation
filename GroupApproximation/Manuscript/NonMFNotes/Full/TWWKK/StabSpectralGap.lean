import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabEntry
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Spectral gaps in the compact operators `𝒦 = Stab ℂ`

A self-adjoint element `x` of the compact operators `𝒦 = Stab ℂ ⊆ B(ℓ²(ℕ, H_ℂ))` has
countable quasispectrum accumulating only at `0`. The form used downstream is a *gap*
statement: every interval `(a, b)` with `0 < a < b` contains a point outside the
quasispectrum (Conway, *A Course in Functional Analysis*, VII.7.1).

## Proof

Suppose `(a, b) ⊆ σₙ(x)`. Pick `N` and a finite matrix `x' = P_N x' P_N` with
`‖h(x)‖ ‖x - x'‖ < 1`, where `h(t) = t / max(t, a)²`, so that `h(t) t = 1` for `t ≥ a`.
Then `N + 1` disjoint bumps `f_i` supported in `(a, b)` give nonzero, self-adjoint,
pairwise orthogonal `y_i = f_i(x) ∈ 𝒦` with `h(x) x y_i = y_i`.

Choose `k_i` with `v_i = y_i (e_{k_i 0} ⊗ 1) ≠ 0`. The `v_i` are pairwise orthogonal in the
sense `v_i^* v_j = 0` for `i ≠ j`, and every combination `u = Σ g_i v_i` satisfies
`h(x) x u = u`. If `P_N u = 0`, then `x' u = 0`, so `‖u‖ ≤ ‖h(x)‖ ‖x - x'‖ ‖u‖` and `u = 0`;
orthogonality then forces `g = 0`. So the `N + 1` vectors `P_N v_i` are linearly
independent. They lie in the span of the `N` matrix units `e_{l 0} ⊗ 1` for `l < N`, which
is a contradiction.

The argument lives inside the algebra (column spaces of `ℕ × ℕ` matrices) and does not use
compactness on `ℓ²(ℕ, H_ℂ)`. This matters because the model `Stab ℂ` has infinite
multiplicity: `H_ℂ` is the space of a faithful representation of `ℂ`.

## Main statement

* `Stab.exists_not_mem_quasispectrum`: for self-adjoint `x : Stab ℂ` and `0 < a < b`,
  some `c ∈ (a, b)` lies outside `quasispectrum ℝ x`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C3gap, work order WO-TWWKK-C3gap; consumed by the q-trick index lane C234).
-/

namespace GroupApproximation.Full.TWWKK

noncomputable section

namespace Stab

namespace SpectralGap

/-! ## Real functions -/

/-- The tent function of height `r` centred at `c`: `t ↦ max 0 (r - |t - c|)`. -/
def bump (c r t : ℝ) : ℝ :=
  max 0 (r - |t - c|)

theorem continuous_bump (c r : ℝ) : Continuous (bump c r) := by
  show Continuous fun t : ℝ => max 0 (r - |t - c|)
  exact continuous_const.max
    (continuous_const.sub (continuous_abs.comp (continuous_id.sub continuous_const)))

theorem bump_zero {c r : ℝ} (hr : 0 ≤ r) (hrc : r ≤ c) : bump c r 0 = 0 := by
  rw [bump, zero_sub, abs_neg, abs_of_nonneg (hr.trans hrc)]
  exact max_eq_left (by linarith)

theorem bump_self {c r : ℝ} (hr : 0 ≤ r) : bump c r c = r := by
  rw [bump, sub_self, abs_zero, sub_zero]
  exact max_eq_right hr

/-- Tents whose centres are at least `2r` apart have disjoint supports. -/
theorem bump_mul_bump {c c' r : ℝ} (h : 2 * r ≤ |c - c'|) (t : ℝ) :
    bump c r t * bump c' r t = 0 := by
  rw [bump, bump]
  rcases le_or_lt (r - |t - c|) 0 with h1 | h1
  · rw [max_eq_left h1, zero_mul]
  · rcases le_or_lt (r - |t - c'|) 0 with h2 | h2
    · rw [max_eq_left h2, mul_zero]
    · exfalso
      have h3 := abs_sub_le c t c'
      rw [abs_sub_comm c t] at h3
      linarith

/-- The function `t ↦ t / max(t, a)²`; it vanishes at `0` and inverts `t` on `[a, ∞)`. -/
def gapInv (a t : ℝ) : ℝ :=
  t / max t a ^ 2

theorem continuous_gapInv {a : ℝ} (ha : 0 < a) : Continuous (gapInv a) :=
  Continuous.div (f := fun t : ℝ => t) (g := fun t : ℝ => max t a ^ 2) continuous_id
    ((continuous_id.max continuous_const).pow 2)
    fun t => pow_ne_zero 2 (ha.trans_le (le_max_right t a)).ne'

theorem gapInv_zero (a : ℝ) : gapInv a 0 = 0 := by
  rw [gapInv, zero_div]

/-- On the support of a tent lying in `(a, ∞)`, `gapInv a t * t = 1`. -/
theorem gapInv_mul_bump {a c r : ℝ} (ha : 0 < a) (hc : a + r ≤ c) (t : ℝ) :
    gapInv a t * (t * bump c r t) = bump c r t := by
  rcases le_or_lt (r - |t - c|) 0 with h | h
  · rw [bump, max_eq_left h, mul_zero, mul_zero]
  · have h1 := neg_abs_le (t - c)
    have ht : a < t := by linarith
    have ht0 : t ≠ 0 := (ha.trans ht).ne'
    rw [gapInv, max_eq_left ht.le]
    calc t / t ^ 2 * (t * bump c r t) = t * t / t ^ 2 * bump c r t := by ring
      _ = bump c r t := by rw [← sq, div_self (pow_ne_zero 2 ht0), one_mul]

/-- The centres `a + 2 i r + r` are `2r`-separated. -/
theorem two_mul_le_abs_sub {a r : ℝ} (hr : 0 < r) {i j : ℕ} (hij : i ≠ j) :
    2 * r ≤ |a + 2 * ((i : ℝ) * r) + r - (a + 2 * ((j : ℝ) * r) + r)| := by
  have e : a + 2 * ((i : ℝ) * r) + r - (a + 2 * ((j : ℝ) * r) + r) =
      2 * ((i : ℝ) * r - (j : ℝ) * r) := by ring
  rw [e]
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have h' : ((i : ℝ) + 1) * r ≤ (j : ℝ) * r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_iff_add_one_le.mp h) hr.le
    rw [add_mul, one_mul] at h'
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h' : ((j : ℝ) + 1) * r ≤ (i : ℝ) * r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_iff_add_one_le.mp h) hr.le
    rw [add_mul, one_mul] at h'
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ## Column spaces of finite matrices -/

theorem rep_eq_smul (d : ℂ) : rep ℂ d = d • rep ℂ 1 :=
  calc rep ℂ d = rep ℂ (d • (1 : ℂ)) := congrArg (rep ℂ) (mul_one d).symm
    _ = d • rep ℂ 1 := map_smul (rep ℂ) d 1

/-- The span of the first `N` matrix units `e_{l 0} ⊗ 1` of the zeroth column. -/
abbrev colSpan (N : ℕ) : Submodule ℂ (Ambient ℂ) :=
  Submodule.span ℂ (Set.range fun l : Fin N => matUnit ℂ (l : ℕ) 0 (rep ℂ 1))

/-- A nonzero element of `𝒦` has a nonzero product with some matrix unit `e_{k 0} ⊗ 1`. -/
theorem exists_mul_ne_zero {Y : Ambient ℂ} (hY : Y ∈ closedSubalgebra ℂ) (hY0 : Y ≠ 0) :
    ∃ k : ℕ, Y * matUnit ℂ k 0 (rep ℂ 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hunit : ∀ (i j : ℕ) (d : ℂ), Y * matUnit ℂ i j (rep ℂ d) = 0 := by
    intro i j d
    have e : matUnit ℂ i j (rep ℂ d) = matUnit ℂ i 0 (rep ℂ 1) * matUnit ℂ 0 j (rep ℂ d) := by
      rw [matUnit_mul_self, ← map_mul (rep ℂ), one_mul]
    rw [e, ← mul_assoc, hcon i, zero_mul]
  have hfin : ∀ z ∈ finiteMatrices ℂ, Y * z = 0 := by
    intro z hz
    obtain ⟨N, hN, hc⟩ := mem_finiteSub.mp (finiteMatrices_le_finiteSub hz)
    rw [← hN, trunc_mul_mul_trunc_eq_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    obtain ⟨d, hd⟩ := (NonUnitalStarAlgHom.mem_range (rep ℂ)).mp (hc i j)
    rw [← hd]
    exact hunit i j d
  have hcl : ∀ z ∈ closedSubalgebra ℂ, Y * z = 0 := by
    intro z hz
    have hz' : z ∈ closure (finiteMatrices ℂ : Set (Ambient ℂ)) := hz
    exact closure_minimal (s := (finiteMatrices ℂ : Set (Ambient ℂ)))
      (t := {w : Ambient ℂ | Y * w = 0}) (fun w hw => hfin w hw)
      (isClosed_eq (continuous_mul_left Y) continuous_const) hz'
  have h := hcl (star Y) (star_mem hY)
  have hn : ‖Y‖ * ‖Y‖ = 0 := by
    rw [← CStarRing.norm_self_mul_star, h, norm_zero]
  exact hY0 (norm_eq_zero.mp (mul_self_eq_zero.mp hn))
