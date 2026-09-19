import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.RelTValuation
import GroupApproximation.PropertyT.IntegralColumnPlaneClosure
import Mathlib.Algebra.Field.GeomSum

/-!
# Relative property (T): the closed mass system on `F_p[X]²`

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2): Thom's Kazhdan group
uses relative property (T) of `(F_p[t,t⁻¹]^3 ⋊ SL_3, F_p[t,t⁻¹]^3)` (A. Thom, Groups Geom. Dyn. 4
(2010), §2.1, Lemma 2.1), proved by Burger's argument (Burger 1991; Shalom 1999; Kassabov 2007, §2).

This file closes Burger's argument for one shear plane `F_p[X]²`.

* `RelTMass.one_le_sq_mul_norm_sub_one_sq`: a nontrivial `p`-th root of unity `ω` satisfies
  `1 ≤ p² ‖ω - 1‖²` (from the vanishing geometric sum).
* `RelTPlane.measureReal_ne_one_le_of_torsion`: if the plane element `vec x` has `p`-torsion
  characters, the mass of the characters nontrivial at `vec x` is at most `p²` times the squared
  displacement by `vec x`.
* `RelTShear.measureReal_regionD_le`: the scalar region `D` is controlled by the displacements of
  `vec (1, 0)` and `vec (0, 1)`.
* `RelTShear.measureReal_regions_le`: the transport inequalities for the shears by `X` and by `1`
  form the closed system of `IntegralColumnPlaneClosure.total_le_of_closed_system`, whence the
  total mass of the four regions is `O((p + 1)² δ²)`.
* `RelTShear.norm_vec_displacement_le`: every plane vector moves a unit vector by at most
  `26 (p + 1) δ`, when the six shear and unit-vector generators move it by at most `δ`.
-/

namespace GroupApproximation.Full.A2ThomT

open WeakDual MeasureTheory Polynomial
open RepresentedRootPlaneSpectralMeasure

noncomputable section

universe u v w

attribute [local instance] RelTPlane.relTPlaneCharacterMeasurableSpace
  RelTPlane.relTPlaneCharacterBorelSpace RelTPlane.relTPlaneSpecMeasureIsFinite

namespace RelTMass

/-- In `F_p[X]` the natural number `p` is zero. -/
theorem natCast_polynomial_self (p : ℕ) : ((p : ℕ) : Polynomial (ZMod p)) = 0 := by
  rw [← Polynomial.C_eq_natCast (R := ZMod p) p, ZMod.natCast_self, map_zero]

/-- For a unit complex number, `‖ωᵏ - 1‖ ≤ k ‖ω - 1‖`. -/
theorem norm_pow_sub_one_le {ω : ℂ} (hω : ‖ω‖ = 1) (k : ℕ) :
    ‖ω ^ k - 1‖ ≤ (k : ℝ) * ‖ω - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : ω ^ (k + 1) - 1 = ω ^ k * (ω - 1) + (ω ^ k - 1) := by ring
    have hnorm : ‖ω ^ k * (ω - 1)‖ = ‖ω - 1‖ := by
      rw [norm_mul, norm_pow, hω, one_pow, one_mul]
    have htri := norm_add_le (ω ^ k * (ω - 1)) (ω ^ k - 1)
    rw [hsplit, Nat.cast_succ]
    rw [hnorm] at htri
    linarith

/-- A nontrivial `p`-th root of unity is at distance at least `1 / p` from `1`. -/
theorem one_le_sq_mul_norm_sub_one_sq {p : ℕ} (hp0 : p ≠ 0) {ω : ℂ} (hω : ‖ω‖ = 1)
    (hpow : ω ^ p = 1) (hne : ω ≠ 1) : 1 ≤ (p : ℝ) ^ 2 * ‖ω - 1‖ ^ 2 := by
  have hgeom : ∑ i ∈ Finset.range p, ω ^ i = 0 := by
    rw [geom_sum_eq hne p, hpow, sub_self, zero_div]
  have hsum : ∑ i ∈ Finset.range p, (1 - ω ^ i) = (p : ℂ) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hbound : (p : ℝ) ≤ (p : ℝ) * ((p : ℝ) * ‖ω - 1‖) := by
    calc (p : ℝ) = ‖∑ i ∈ Finset.range p, (1 - ω ^ i)‖ := by
          rw [hsum, Complex.norm_natCast]
      _ ≤ ∑ i ∈ Finset.range p, ‖1 - ω ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range p, (p : ℝ) * ‖ω - 1‖ := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_sub_rev]
          have hip : (i : ℝ) ≤ p := by
            have hlt := Finset.mem_range.mp hi
            exact_mod_cast hlt.le
          calc ‖ω ^ i - 1‖ ≤ (i : ℝ) * ‖ω - 1‖ := norm_pow_sub_one_le hω i
            _ ≤ (p : ℝ) * ‖ω - 1‖ := mul_le_mul_of_nonneg_right hip (norm_nonneg _)
      _ = (p : ℝ) * ((p : ℝ) * ‖ω - 1‖) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hp : (0 : ℝ) < p := by
    exact_mod_cast Nat.pos_of_ne_zero hp0
  have hone : 1 ≤ (p : ℝ) * ‖ω - 1‖ := by
    by_contra hlt
    push_neg at hlt
    have hmul := mul_lt_mul_of_pos_left hlt hp
    linarith
  calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
    _ ≤ ((p : ℝ) * ‖ω - 1‖) ^ 2 := pow_le_pow_left₀ zero_le_one hone 2
    _ = (p : ℝ) ^ 2 * ‖ω - 1‖ ^ 2 := mul_pow _ _ _

end RelTMass

namespace RelTPlane

variable {G : Type u} [Group G] {V : Type w} [AddCommGroup V] (Q : RelTPlane G V)
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (rho : G →* (E ≃ₗᵢ[ℝ] E))

/-- **Torsion mass bound.**  If every character is a `p`-th root of unity at `vec x`, the mass of
the characters nontrivial at `vec x` is at most `p²` times the squared displacement by `vec x`. -/
theorem measureReal_ne_one_le_of_torsion (z : E) (hz : ‖z‖ = 1) (x : V) {p : ℕ} (hp0 : p ≠ 0)
    (htors : ∀ chi : characterSpace ℂ (Q.represented rho).algebra,
      chi ((Q.represented rho).coordinate x) ^ p = 1) :
    (Q.specMeasure rho z hz).real
        {chi : characterSpace ℂ (Q.represented rho).algebra |
          chi ((Q.represented rho).coordinate x) ≠ 1} ≤
      (p : ℝ) ^ 2 * ‖rho (Q.vec x) z - z‖ ^ 2 := by
  have hS := Q.measurableSet_chi_coordinate_ne_one rho x
  have hcont : Continuous (fun chi : characterSpace ℂ (Q.represented rho).algebra ↦
      (p : ℝ) ^ 2 * ‖chi ((Q.represented rho).coordinate x) - 1‖ ^ 2) :=
    continuous_const.mul (((Q.continuous_chi_coordinate rho x).sub continuous_const).norm.pow 2)
  have hint1 : Integrable (fun chi : characterSpace ℂ (Q.represented rho).algebra ↦
      (p : ℝ) ^ 2 * ‖chi ((Q.represented rho).coordinate x) - 1‖ ^ 2)
      (Q.specMeasure rho z hz) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable
      ({chi : characterSpace ℂ (Q.represented rho).algebra |
          chi ((Q.represented rho).coordinate x) ≠ 1}.indicator fun _ ↦ (1 : ℝ))
      (Q.specMeasure rho z hz) :=
    (integrable_const (1 : ℝ)).indicator hS
  have hpoint : ∀ chi : characterSpace ℂ (Q.represented rho).algebra,
      {chi' : characterSpace ℂ (Q.represented rho).algebra |
          chi' ((Q.represented rho).coordinate x) ≠ 1}.indicator (fun _ ↦ (1 : ℝ)) chi ≤
        (p : ℝ) ^ 2 * ‖chi ((Q.represented rho).coordinate x) - 1‖ ^ 2 := by
    intro chi
    by_cases hchi : chi ((Q.represented rho).coordinate x) = 1
    · have hnot : chi ∉ {chi' : characterSpace ℂ (Q.represented rho).algebra |
          chi' ((Q.represented rho).coordinate x) ≠ 1} := fun h ↦ h hchi
      rw [Set.indicator_of_notMem hnot]
      positivity
    · have hmem : chi ∈ {chi' : characterSpace ℂ (Q.represented rho).algebra |
          chi' ((Q.represented rho).coordinate x) ≠ 1} := hchi
      rw [Set.indicator_of_mem hmem]
      exact RelTMass.one_le_sq_mul_norm_sub_one_sq hp0 (Q.norm_chi_coordinate rho chi x)
        (htors chi) hchi
  have hmono := integral_mono hint2 hint1 hpoint
  rw [integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one, integral_const_mul,
    Q.integral_displacement_sq rho z hz x] at hmono
  exact hmono

end RelTPlane

namespace RelTShear

variable {G : Type u} [Group G] {p : ℕ} (S : RelTShear G p)
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (rho : G →* (E ≃ₗᵢ[ℝ] E))

theorem chi_coordinate_natCast_fst
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    chi ((S.toRelTPlane.represented rho).coordinate ((n : Polynomial (ZMod p)), 0)) =
      chi ((S.toRelTPlane.represented rho).coordinate (1, 0)) ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero]
    exact S.toRelTPlane.chi_coordinate_zero rho chi
  | succ n ih =>
    rw [Nat.cast_succ, S.chi_coordinate_add_fst rho chi, ih, pow_succ]

theorem chi_coordinate_natCast_snd
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) (n : ℕ) :
    chi ((S.toRelTPlane.represented rho).coordinate (0, (n : Polynomial (ZMod p)))) =
      chi ((S.toRelTPlane.represented rho).coordinate (0, 1)) ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero]
    exact S.toRelTPlane.chi_coordinate_zero rho chi
  | succ n ih =>
    rw [Nat.cast_succ, S.chi_coordinate_add_snd rho chi, ih, pow_succ]

theorem pow_chi_coordinate_fst
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :
    chi ((S.toRelTPlane.represented rho).coordinate (1, 0)) ^ p = 1 := by
  rw [← S.chi_coordinate_natCast_fst rho chi p, RelTMass.natCast_polynomial_self]
  exact S.toRelTPlane.chi_coordinate_zero rho chi

theorem pow_chi_coordinate_snd
    (chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra) :
    chi ((S.toRelTPlane.represented rho).coordinate (0, 1)) ^ p = 1 := by
  rw [← S.chi_coordinate_natCast_snd rho chi p, RelTMass.natCast_polynomial_self]
  exact S.toRelTPlane.chi_coordinate_zero rho chi

/-- The scalar region is controlled by the displacements of `vec (1, 0)` and `vec (0, 1)`. -/
theorem measureReal_regionD_le (z : E) (hz : ‖z‖ = 1) (hp0 : p ≠ 0) :
    (S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho) ≤
      (p : ℝ) ^ 2 * (‖rho (S.vec (1, 0)) z - z‖ ^ 2 + ‖rho (S.vec (0, 1)) z - z‖ ^ 2) := by
  have hsub : S.regionD rho ⊆
      {chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra |
          chi ((S.toRelTPlane.represented rho).coordinate (1, 0)) ≠ 1} ∪
        {chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra |
          chi ((S.toRelTPlane.represented rho).coordinate (0, 1)) ≠ 1} := by
    intro chi hchi
    have hor : S.lam rho chi 0 ≠ 1 ∨ S.mu rho chi 0 ≠ 1 := hchi
    have hl : S.lam rho chi 0 = chi ((S.toRelTPlane.represented rho).coordinate (1, 0)) := by
      show chi ((S.toRelTPlane.represented rho).coordinate (X ^ 0, 0)) = _
      rw [pow_zero]
    have hm : S.mu rho chi 0 = chi ((S.toRelTPlane.represented rho).coordinate (0, 1)) := by
      show chi ((S.toRelTPlane.represented rho).coordinate (0, X ^ 0)) = _
      rw [pow_zero]
    rcases hor with h | h
    · apply Set.mem_union_left
      show chi ((S.toRelTPlane.represented rho).coordinate (1, 0)) ≠ 1
      rw [← hl]
      exact h
    · apply Set.mem_union_right
      show chi ((S.toRelTPlane.represented rho).coordinate (0, 1)) ≠ 1
      rw [← hm]
      exact h
  have hmono := measureReal_mono (μ := S.toRelTPlane.specMeasure rho z hz) hsub
  have hunion := measureReal_union_le (μ := S.toRelTPlane.specMeasure rho z hz)
    {chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra |
      chi ((S.toRelTPlane.represented rho).coordinate (1, 0)) ≠ 1}
    {chi : characterSpace ℂ (S.toRelTPlane.represented rho).algebra |
      chi ((S.toRelTPlane.represented rho).coordinate (0, 1)) ≠ 1}
  have hfst := S.toRelTPlane.measureReal_ne_one_le_of_torsion rho z hz (1, 0) hp0
    (S.pow_chi_coordinate_fst rho)
  have hsnd := S.toRelTPlane.measureReal_ne_one_le_of_torsion rho z hz (0, 1) hp0
    (S.pow_chi_coordinate_snd rho)
  rw [mul_add]
  linarith

/-- Transport by the shear `up X`: `√(μ A + μ B) ≤ √(μ C + μ D) + δ`. -/
theorem sqrt_measureReal_AB_le (z : E) (hz : ‖z‖ = 1) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hupX : ‖rho (S.up X) z - z‖ ≤ delta) :
    Real.sqrt ((S.toRelTPlane.specMeasure rho z hz).real (S.regionA rho) +
        (S.toRelTPlane.specMeasure rho z hz).real (S.regionB rho)) ≤
      Real.sqrt ((S.toRelTPlane.specMeasure rho z hz).real (S.regionC rho) +
        (S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho)) + delta := by
  have h := S.toRelTPlane.sqrt_measureReal_le_of_mapsTo rho z hz (S.up X) (S.up_normalizes X)
    (S.up_inv_normalizes X) hdelta hupX
    ((S.measurableSet_regionA rho).union (S.measurableSet_regionB rho)) (S.mapsTo_upX rho)
  rw [measureReal_union (μ := S.toRelTPlane.specMeasure rho z hz)
    (S.disjoint_regionA_regionB rho) (S.measurableSet_regionB rho)] at h
  have hCD := Real.sqrt_le_sqrt (measureReal_union_le (μ := S.toRelTPlane.specMeasure rho z hz)
    (S.regionC rho) (S.regionD rho))
  linarith

/-- Transport by the shear `low X`: `√(μ C + μ B) ≤ √(μ A + μ D) + δ`. -/
theorem sqrt_measureReal_CB_le (z : E) (hz : ‖z‖ = 1) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlowX : ‖rho (S.low X) z - z‖ ≤ delta) :
    Real.sqrt ((S.toRelTPlane.specMeasure rho z hz).real (S.regionC rho) +
        (S.toRelTPlane.specMeasure rho z hz).real (S.regionB rho)) ≤
      Real.sqrt ((S.toRelTPlane.specMeasure rho z hz).real (S.regionA rho) +
        (S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho)) + delta := by
  have h := S.toRelTPlane.sqrt_measureReal_le_of_mapsTo rho z hz (S.low X) (S.low_normalizes X)
    (S.low_inv_normalizes X) hdelta hlowX
    ((S.measurableSet_regionC rho).union (S.measurableSet_regionB rho)) (S.mapsTo_lowX rho)
  rw [measureReal_union (μ := S.toRelTPlane.specMeasure rho z hz)
    (S.disjoint_regionC_regionB rho) (S.measurableSet_regionB rho)] at h
  have hAD := Real.sqrt_le_sqrt (measureReal_union_le (μ := S.toRelTPlane.specMeasure rho z hz)
    (S.regionA rho) (S.regionD rho))
  linarith

/-- **Closed system.**  If the shears by `X` and by `1` and the unit vectors of the plane move a
unit vector by at most `δ`, the four regions carry total mass at most `168 (p + 1)² δ²`. -/
theorem measureReal_regions_le [NeZero p] (z : E) (hz : ‖z‖ = 1) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hupX : ‖rho (S.up X) z - z‖ ≤ delta) (hlowX : ‖rho (S.low X) z - z‖ ≤ delta)
    (hup1 : ‖rho (S.up 1) z - z‖ ≤ delta) (hlow1 : ‖rho (S.low 1) z - z‖ ≤ delta)
    (hfst : ‖rho (S.vec (1, 0)) z - z‖ ≤ delta) (hsnd : ‖rho (S.vec (0, 1)) z - z‖ ≤ delta) :
    (S.toRelTPlane.specMeasure rho z hz).real (S.regionA rho) +
        (S.toRelTPlane.specMeasure rho z hz).real (S.regionB rho) +
        (S.toRelTPlane.specMeasure rho z hz).real (S.regionC rho) +
        (S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho) ≤
      168 * ((p : ℝ) + 1) ^ 2 * delta ^ 2 := by
  have h1 := S.sqrt_measureReal_AB_le rho z hz hdelta hupX
  have h2 := S.sqrt_measureReal_CB_le rho z hz hdelta hlowX
  have h3 := S.toRelTPlane.sqrt_measureReal_le_of_mapsTo rho z hz (S.up 1) (S.up_normalizes 1)
    (S.up_inv_normalizes 1) hdelta hup1 (S.measurableSet_regionA rho) (S.mapsTo_up1 rho)
  have h4 := S.toRelTPlane.sqrt_measureReal_le_of_mapsTo rho z hz (S.low 1) (S.low_normalizes 1)
    (S.low_inv_normalizes 1) hdelta hlow1 (S.measurableSet_regionC rho) (S.mapsTo_low1 rho)
  have hD := S.measureReal_regionD_le rho z hz (NeZero.ne p)
  have e1 := pow_le_pow_left₀ (norm_nonneg _) hfst 2
  have e2 := pow_le_pow_left₀ (norm_nonneg _) hsnd 2
  have e3 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) (sq_nonneg (p : ℝ))
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hd : (S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho) ≤
      (2 * (p : ℝ) * delta) ^ 2 := by
    have hpd := mul_nonneg (sq_nonneg (p : ℝ)) (sq_nonneg delta)
    have hexp : (2 * (p : ℝ) * delta) ^ 2 = 4 * ((p : ℝ) ^ 2 * delta ^ 2) := by ring
    have hexp' : (p : ℝ) ^ 2 * (delta ^ 2 + delta ^ 2) = 2 * ((p : ℝ) ^ 2 * delta ^ 2) := by
      ring
    rw [hexp]
    rw [hexp'] at e3
    linarith
  have hsd : Real.sqrt ((S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho)) ≤
      2 * (p : ℝ) * delta := by
    have hroot := Real.sqrt_le_sqrt hd
    rw [Real.sqrt_sq (mul_nonneg (mul_nonneg zero_le_two hp) hdelta)] at hroot
    exact hroot
  have htotal := IntegralColumnPlaneClosure.total_le_of_closed_system measureReal_nonneg
    measureReal_nonneg measureReal_nonneg measureReal_nonneg hdelta hdelta h1 h2 h3 h4
  have hV : Real.sqrt ((S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho)) + delta +
      delta ≤ 2 * ((p : ℝ) + 1) * delta := by
    linarith
  have hVnn : 0 ≤ Real.sqrt ((S.toRelTPlane.specMeasure rho z hz).real (S.regionD rho)) +
      delta + delta :=
    add_nonneg (add_nonneg (Real.sqrt_nonneg _) hdelta) hdelta
  have hsq := pow_le_pow_left₀ hVnn hV 2
  have hexp : (2 * ((p : ℝ) + 1) * delta) ^ 2 = 4 * (((p : ℝ) + 1) ^ 2 * delta ^ 2) := by ring
  rw [hexp] at hsq
  have hfinal : 168 * ((p : ℝ) + 1) ^ 2 * delta ^ 2 =
      42 * (4 * (((p : ℝ) + 1) ^ 2 * delta ^ 2)) := by
    ring
  rw [hfinal]
  linarith

/-- **Per-plane bound.**  If the shears by `X` and by `1` and the unit vectors of the plane move a
unit vector by at most `δ`, every plane vector moves it by at most `26 (p + 1) δ`. -/
theorem norm_vec_displacement_le [NeZero p] (z : E) (hz : ‖z‖ = 1) {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hupX : ‖rho (S.up X) z - z‖ ≤ delta) (hlowX : ‖rho (S.low X) z - z‖ ≤ delta)
    (hup1 : ‖rho (S.up 1) z - z‖ ≤ delta) (hlow1 : ‖rho (S.low 1) z - z‖ ≤ delta)
    (hfst : ‖rho (S.vec (1, 0)) z - z‖ ≤ delta) (hsnd : ‖rho (S.vec (0, 1)) z - z‖ ≤ delta)
    (a b : Polynomial (ZMod p)) :
    ‖rho (S.vec (a, b)) z - z‖ ≤ 26 * ((p : ℝ) + 1) * delta := by
  have hdisp := S.toRelTPlane.displacement_sq_le rho z hz (a, b)
    (S.regionA rho ∪ S.regionB rho ∪ S.regionC rho ∪ S.regionD rho)
    ((((S.measurableSet_regionA rho).union (S.measurableSet_regionB rho)).union
      (S.measurableSet_regionC rho)).union (S.measurableSet_regionD rho))
    (fun chi h ↦ S.mem_regions_of_ne_one rho chi a b h)
  have hregions := S.measureReal_regions_le rho z hz hdelta hupX hlowX hup1 hlow1 hfst hsnd
  have u1 := measureReal_union_le (μ := S.toRelTPlane.specMeasure rho z hz)
    (S.regionA rho ∪ S.regionB rho ∪ S.regionC rho) (S.regionD rho)
  have u2 := measureReal_union_le (μ := S.toRelTPlane.specMeasure rho z hz)
    (S.regionA rho ∪ S.regionB rho) (S.regionC rho)
  have u3 := measureReal_union_le (μ := S.toRelTPlane.specMeasure rho z hz)
    (S.regionA rho) (S.regionB rho)
  have hpd := sq_nonneg (((p : ℝ) + 1) * delta)
  have hexp : (26 * ((p : ℝ) + 1) * delta) ^ 2 = 676 * (((p : ℝ) + 1) ^ 2 * delta ^ 2) := by
    ring
  have hexp' : (((p : ℝ) + 1) * delta) ^ 2 = ((p : ℝ) + 1) ^ 2 * delta ^ 2 := by ring
  have hreg' : 168 * ((p : ℝ) + 1) ^ 2 * delta ^ 2 = 168 * (((p : ℝ) + 1) ^ 2 * delta ^ 2) := by
    ring
  rw [hexp'] at hpd
  rw [hreg'] at hregions
  have hsq : ‖rho (S.vec (a, b)) z - z‖ ^ 2 ≤ (26 * ((p : ℝ) + 1) * delta) ^ 2 := by
    rw [hexp]
    linarith
  have hnn : 0 ≤ 26 * ((p : ℝ) + 1) * delta := mul_nonneg (by positivity) hdelta
  exact (sq_le_sq₀ (norm_nonneg _) hnn).mp hsq

end RelTShear

end

end GroupApproximation.Full.A2ThomT
