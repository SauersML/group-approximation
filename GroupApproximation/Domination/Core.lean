import GroupApproximation.Sofic.SoficAmplification
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Exponential

/-!
# Power amplification turns qualitative collapse into a linear bound

This file isolates the quantitative engine behind the domination-constant
formulation of hyperlinear versus sofic.  The input is a family of defects in
`[0,1]` closed under Cartesian/tensor powers, with the classical Bernoulli law

`q(x^[m], g) = 1 - (1 - q(x,g))^m`.

The power construction is standard in sofic approximation and in unitary
tensor-amplification arguments.  The contribution formalized here is the
abstract linearization statement: for a fixed finite relator set, qualitative
collapse of one marked word as the relator defect tends to zero is equivalent
to a single global linear domination inequality.

No group-specific input is hidden in the proof.  Later files instantiate the
system with finite permutation actions and finite-dimensional unitary
representations.  The estimate uses only Bernoulli's inequality and the
classical bound `1 - x ≤ exp(-x)`.
-/

namespace GroupApproximation

open scoped BigOperators

/-- A family of `[0,1]`-valued defects with the exact Cartesian/tensor-power
law.  The parameter `ι` will be a group and `Model` a class of finite models. -/
structure PowerDefectSystem (ι Model : Type*) where
  defect : Model → ι → ℝ
  power : Model → ℕ → Model
  defect_nonneg : ∀ x g, 0 ≤ defect x g
  defect_le_one : ∀ x g, defect x g ≤ 1
  defect_power : ∀ x m g,
    defect (power x m) g = 1 - (1 - defect x g) ^ m

namespace PowerDefectSystem

variable {ι Model : Type*} (D : PowerDefectSystem ι Model)

/-- Total defect of a finite relator set. -/
def totalDefect (R : Finset ι) (x : Model) : ℝ :=
  ∑ r ∈ R, D.defect x r

theorem totalDefect_nonneg (R : Finset ι) (x : Model) :
    0 ≤ D.totalDefect R x := by
  exact Finset.sum_nonneg fun r _ ↦ D.defect_nonneg x r

/-- A power inflates total relator defect by at most its exponent.  This is
the union bound/Bernoulli estimate used in the classical sofic amplification
argument. -/
theorem totalDefect_power_le (R : Finset ι) (x : Model) (m : ℕ) :
    D.totalDefect R (D.power x m) ≤ m * D.totalDefect R x := by
  unfold totalDefect
  calc
    (∑ r ∈ R, D.defect (D.power x m) r) =
        ∑ r ∈ R, (1 - (1 - D.defect x r) ^ m) := by
          apply Finset.sum_congr rfl
          intro r _
          exact D.defect_power x m r
    _ ≤ ∑ r ∈ R, (m : ℝ) * D.defect x r := by
          apply Finset.sum_le_sum
          intro r _
          exact one_sub_pow_le (D.defect_le_one x r) m
    _ = (m : ℝ) * ∑ r ∈ R, D.defect x r := by
          rw [Finset.mul_sum]

/-- Epsilon--delta form of the qualitative radical criterion: the marked
defect vanishes uniformly whenever total relator defect vanishes. -/
def VanishesAtZero (R : Finset ι) (w : ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x : Model, D.totalDefect R x < δ → D.defect x w < ε

/-- A single finite linear domination constant for the marked defect. -/
def HasLinearDomination (R : Finset ι) (w : ι) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : Model, D.defect x w ≤ C * D.totalDefect R x

/-- A linear domination inequality immediately implies qualitative collapse. -/
theorem vanishesAtZero_of_hasLinearDomination {R : Finset ι} {w : ι}
    (h : D.HasLinearDomination R w) : D.VanishesAtZero R w := by
  obtain ⟨C, hC, hdom⟩ := h
  intro ε hε
  refine ⟨ε / (C + 1), div_pos hε (by linarith), ?_⟩
  intro x hx
  calc
    D.defect x w ≤ C * D.totalDefect R x := hdom x
    _ ≤ (C + 1) * D.totalDefect R x := by
      exact mul_le_mul_of_nonneg_right (by linarith) (D.totalDefect_nonneg R x)
    _ < (C + 1) * (ε / (C + 1)) := by
      exact mul_lt_mul_of_pos_left hx (by linarith)
    _ = ε := by field_simp

/-- The quantitative power boost used in the converse.  Taking
`m = ceil(1/b)` makes `1 - (1-b)^m` at least `1-exp(-1)`, while
`m < 2/b`. -/
theorem exists_power_boost {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ∃ m : ℕ,
      (m : ℝ) < 2 / b ∧
      1 - Real.exp (-1) ≤ 1 - (1 - b) ^ m := by
  let m : ℕ := ⌈1 / b⌉₊
  have hinv0 : 0 ≤ 1 / b := by positivity
  have hm_lower : 1 / b ≤ (m : ℝ) := by
    exact Nat.le_ceil (1 / b)
  have hm_upper : (m : ℝ) < 1 / b + 1 := by
    simpa [m] using Nat.ceil_lt_add_one hinv0
  have hone_le_inv : 1 ≤ 1 / b := by
    rw [le_div_iff₀ hb0]
    simpa using hb1
  have hm_two : (m : ℝ) < 2 / b := by
    calc
      (m : ℝ) < 1 / b + 1 := hm_upper
      _ ≤ 2 * (1 / b) := by linarith
      _ = 2 / b := by ring
  have hmb : 1 ≤ (m : ℝ) * b := by
    have h := mul_le_mul_of_nonneg_right hm_lower hb0.le
    have hcancel : (1 / b) * b = 1 := by field_simp
    rwa [hcancel] at h
  have hbase : 0 ≤ 1 - b := sub_nonneg.mpr hb1
  have hpow_exp : (1 - b) ^ m ≤ (Real.exp (-b)) ^ m := by
    gcongr
    exact Real.one_sub_le_exp_neg b
  have hexp : (Real.exp (-b)) ^ m ≤ Real.exp (-1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) * (-b) ≤ -1 := by nlinarith
    simpa [mul_neg] using this
  refine ⟨m, hm_two, ?_⟩
  linarith [hpow_exp.trans hexp]

/-- **Power linearization theorem.**  For any power-closed `[0,1]` defect
system, qualitative collapse of a marked word is equivalent to a global
linear domination inequality over the same finite relator set.

This is the formal quantitative heart of both the sofic-radical and the
hyperlinear-radical domination constants. -/
theorem hasLinearDomination_of_vanishesAtZero {R : Finset ι} {w : ι}
    (h : D.VanishesAtZero R w) : D.HasLinearDomination R w := by
  have hc : 0 < 1 - Real.exp (-1) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  obtain ⟨δ, hδ, hcollapse⟩ := h (1 - Real.exp (-1)) hc
  refine ⟨2 / δ, by positivity, ?_⟩
  intro x
  let a : ℝ := D.totalDefect R x
  let b : ℝ := D.defect x w
  have ha : 0 ≤ a := D.totalDefect_nonneg R x
  have hb0 : 0 ≤ b := D.defect_nonneg x w
  have hb1 : b ≤ 1 := D.defect_le_one x w
  by_cases hb : b = 0
  · change b ≤ (2 / δ) * a
    rw [hb]
    exact mul_nonneg (by positivity) ha
  have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
  by_contra hnot
  have hratio : (2 / δ) * a < b := lt_of_not_ge hnot
  obtain ⟨m, hm, hboost⟩ := exists_power_boost hbpos hb1
  have hdiv : 2 * a / δ < b := by
    calc
      2 * a / δ = (2 / δ) * a := by ring
      _ < b := hratio
  have htwo : 2 * a < b * δ := (div_lt_iff₀ hδ).mp hdiv
  have hab : 2 * a / b < δ := by
    rw [div_lt_iff₀ hbpos]
    nlinarith
  have hma : (m : ℝ) * a < δ := by
    calc
      (m : ℝ) * a ≤ (2 / b) * a :=
        mul_le_mul_of_nonneg_right hm.le ha
      _ = 2 * a / b := by ring
      _ < δ := hab
  have htotal : D.totalDefect R (D.power x m) < δ :=
    lt_of_le_of_lt (D.totalDefect_power_le R x m) hma
  have hwsmall := hcollapse (D.power x m) htotal
  have hwpower := D.defect_power x m w
  rw [hwpower] at hwsmall
  exact (not_lt_of_ge hboost hwsmall).elim

theorem vanishesAtZero_iff_hasLinearDomination (R : Finset ι) (w : ι) :
    D.VanishesAtZero R w ↔ D.HasLinearDomination R w :=
  ⟨D.hasLinearDomination_of_vanishesAtZero,
    D.vanishesAtZero_of_hasLinearDomination⟩

end PowerDefectSystem

end GroupApproximation
