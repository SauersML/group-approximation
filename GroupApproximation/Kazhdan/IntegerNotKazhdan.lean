import GroupApproximation.Kazhdan.Kazhdan
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The infinite cyclic group is not Kazhdan

Corollary 9.4 of the ascending-HNN dossier.  Property `(T)` passes to quotients,
so a group surjecting onto `ℤ` cannot be Kazhdan.  The witness is the family of
rotation representations: for a small angle `t` the rotation by `t` moves the
unit vector `1 ∈ ℂ` by less than any prescribed `ε` on any prescribed finite set
of exponents, while a nontrivial rotation of the plane fixes no nonzero vector.

The ambient group of the ascending-HNN construction surjects onto `ℤ` through
its height homomorphism, so this is exactly what separates it from the
Kun--Thom examples, in which the ambient group is also Kazhdan.
-/

namespace GroupApproximation

open Complex

/-- The rotation representation of `ℤ` by a fixed angle. -/
noncomputable def rotationRep (t : ℝ) : Multiplicative ℤ →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
  rotation.comp (zpowersHom Circle (Circle.exp t))

theorem rotationRep_apply (t : ℝ) (n : Multiplicative ℤ) (z : ℂ) :
    rotationRep t n z
      = Complex.exp (((((Multiplicative.toAdd n : ℤ) : ℝ) * t : ℝ) : ℂ) * I) * z := by
  simp only [rotationRep, MonoidHom.comp_apply, zpowersHom_apply, rotation_apply,
    Circle.coe_zpow, Circle.coe_exp]
  congr 2
  rw [← Complex.exp_int_mul]
  push_cast
  ring_nf

/-- **The infinite cyclic group is not Kazhdan.** -/
theorem not_hasKazhdanPropertyT_multiplicative_int :
    ¬ HasKazhdanPropertyT.{0, 0} (Multiplicative ℤ) := by
  rintro ⟨Q, ε, hε, hpair⟩
  classical
  set N : ℕ := Q.sup fun q => (Multiplicative.toAdd q).natAbs with hN
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set t : ℝ := min (1 / ((N : ℝ) + 1)) (ε / (4 * ((N : ℝ) + 1))) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have htle : t ≤ 1 / ((N : ℝ) + 1) := min_le_left _ _
  have htle' : t ≤ ε / (4 * ((N : ℝ) + 1)) := min_le_right _ _
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have htone : t ≤ 1 := by
    refine le_trans htle ?_
    rw [div_le_one hNpos]; linarith
  have htlt : t < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  -- a nontrivial rotation has no nonzero fixed vector
  have hzeta : Complex.exp ((t : ℂ) * I) ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h2 : (t : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ)) := by
      refine mul_right_cancel₀ Complex.I_ne_zero ?_
      rw [hn]; ring
    have h3 : t = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
    have hpi := Real.pi_pos
    rcases lt_trichotomy n 0 with hneg | hzero | hpos
    · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
      nlinarith
    · rw [hzero] at h3; simp at h3; linarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
      nlinarith
  -- the unit vector `1` is almost invariant on `Q`
  have halmost : ∀ q ∈ Q, ‖rotationRep t q (1 : ℂ) - (1 : ℂ)‖ < ε := by
    intro q hq
    set n : ℤ := Multiplicative.toAdd q with hndef
    have hnN : n.natAbs ≤ N := by
      rw [hN, hndef]
      exact Finset.le_sup hq
    have hn : ((n.natAbs : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have habs : |(n : ℝ)| ≤ (N : ℝ) := by
      have hbounds : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by omega
      rw [abs_le]
      exact ⟨by exact_mod_cast hbounds.1, by exact_mod_cast hbounds.2⟩
    have habs0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
    have hz : ‖((((n : ℝ) * t : ℝ)) : ℂ) * I‖ = |(n : ℝ)| * t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, abs_of_pos htpos]
    have hzle : ‖((((n : ℝ) * t : ℝ)) : ℂ) * I‖ ≤ 1 := by
      rw [hz]
      calc |(n : ℝ)| * t ≤ (N : ℝ) * (1 / ((N : ℝ) + 1)) :=
            mul_le_mul habs htle htpos.le hNnn
        _ ≤ 1 := by rw [mul_one_div, div_le_one hNpos]; linarith
    have hbound := Complex.norm_exp_sub_one_le hzle
    rw [hz] at hbound
    rw [rotationRep_apply, mul_one]
    refine lt_of_le_of_lt hbound ?_
    have h4 : |(n : ℝ)| * t ≤ (N : ℝ) * (ε / (4 * ((N : ℝ) + 1))) :=
      mul_le_mul habs htle' htpos.le hNnn
    have hpos4 : (0 : ℝ) < 4 * ((N : ℝ) + 1) := by positivity
    have hkey : (N : ℝ) * (ε / (4 * ((N : ℝ) + 1))) < ε / 2 := by
      have h1 : (N : ℝ) * (ε / (4 * ((N : ℝ) + 1)))
          = ε * ((N : ℝ) / (4 * ((N : ℝ) + 1))) := by ring
      rw [h1]
      have h2 : (N : ℝ) / (4 * ((N : ℝ) + 1)) < 1 / 2 := by
        rw [div_lt_div_iff₀ hpos4 (by norm_num : (0:ℝ) < 2)]
        nlinarith
      nlinarith
    linarith
  obtain ⟨y, hy0, hyinv⟩ := hpair ℂ (rotationRep t) (1 : ℂ) norm_one halmost
  have hfix := hyinv (Multiplicative.ofAdd (1 : ℤ))
  have htoAdd : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ℤ))) = 1 := rfl
  rw [rotationRep_apply, htoAdd] at hfix
  simp only [Int.cast_one, one_mul] at hfix
  have hmul : (Complex.exp ((t : ℂ) * I) - 1) * y = 0 := by
    rw [sub_mul, one_mul, hfix, sub_self]
  rcases mul_eq_zero.mp hmul with h | h
  · exact hzeta (sub_eq_zero.mp h)
  · exact hy0 h

/-- A group with a surjection onto `ℤ` is not Kazhdan. -/
theorem not_hasKazhdanPropertyT_of_surjective_onto_int {G : Type u} [Group G]
    (f : G →* Multiplicative ℤ) (hf : Function.Surjective f) :
    ¬ HasKazhdanPropertyT.{u, 0} G := fun hG =>
  not_hasKazhdanPropertyT_multiplicative_int (hG.of_surjective f hf)

end GroupApproximation
