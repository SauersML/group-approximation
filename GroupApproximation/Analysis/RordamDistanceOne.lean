import GroupApproximation.Analysis.CFCStarMulSelfIntertwine
import GroupApproximation.Analysis.DistanceToInvertibles
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Rørdam: a C⋆-algebra without stable rank one has an element at distance one

> **Theorem** (Rørdam, *Advances in the theory of unitary rank and regular
> approximation*, Ann. of Math. 128 (1988), Theorem 2.6).  If the invertible elements
> of a unital C⋆-algebra `A` are not dense, then there is `b ∈ A` with
> `‖b‖ = 1 = dist(b, GL(A))`.

This is the step of Dykema–Haagerup–Rørdam (Duke 90 (1997), proof of their Theorem
3.8) and of Dykema–de la Harpe (J. Math. Pures Appl. 78 (1999), Theorem 1.4) that
turns the estimate `dist(y, GL) ≤ ‖y‖₂` into density of the invertibles: a faithful
tracial state forces such a `b` to be unitary.

## The proof, following Farah–Rørdam, with the continuous functional calculus only

Farah and Rørdam (Münster J. Math. 10 (2017), Lemma 1, Lemma 2, Proposition 3,
Corollary 4) prove it with the polar decomposition and spectral projections in
`B(H)`.  Neither is needed:

* **Lemma 1 is replaced by one line.**  If `z` is invertible and `‖x − z‖ < γ`, then
  `x + (z − x) = z` is invertible, and `z − x` is the only property of Farah–Rørdam's
  `βw` the argument uses.
* **Lemma 2** (`exists_isUnit_cfc_mul_eq`).  With `p = x·ρ(x^*x)`,
  `ρ(u) = max(u, γ²)⁻¹`, we have `‖p‖ ≤ γ⁻¹`, so `e = 1 + p^*(z − x)` is invertible,
  and `s = z e⁻¹ φ(x^*x)` with `φ(u) = max(√u, γ)⁻¹` satisfies
  `G(xx^*) s = x (G·φ)(x^*x)` for every continuous `G` vanishing on `(−∞, γ²]`.
  The identity is `G(xx^*)·x p^* = G(xx^*)`, i.e. `G(u)·uρ(u) = G(u)`, carried
  through the intertwining `x f(x^*x) = f(xx^*) x` (`Analysis/CFCStarMulSelfIntertwine`).
  In the language of the polar decomposition this is `(1 − f_γ) s = (1 − f_γ) v`.
* **Proposition 3 and Corollary 4** (`exists_norm_eq_one_distGL_eq_one`).  For `a`
  with `γ = dist(a, GL) > 0` put `b = a·φ_γ(a^*a)`.  If `dist(b, GL) < β < 1`, Lemma 2
  for `b` at `β` with `G(v) = max(√v − β, 0)` gives an invertible `s` with
  `K(aa^*)·s = a·L(a^*a)`, where `K`, `L` are explicit.  With `M(u) = max(γ, (√u − γβ)/(1−β))`
  one has `M·K = (√u − γβ)₊`, so `w = (M·K)(aa^*)·s` is a positive element times an
  invertible, a limit of invertibles, and `‖a − w‖ = sup_{t ∈ |a|-spectrum}
  min(t, γβ) ≤ γβ < γ`: a contradiction.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (stable rank one of `C*_r(Q)`, the
Gerasimova–Osin citation).  Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace RordamDistanceOne

open DistanceToInvertibles CFCIntertwine

/-! ## The real functions -/

/-- `u ↦ max(√u, γ)⁻¹`; on `x^*x` it is `max(|x|, γ)⁻¹`. -/
noncomputable def phi (γ u : ℝ) : ℝ := (max (Real.sqrt u) γ)⁻¹

/-- `u ↦ max(u, γ²)⁻¹`; on `x^*x` it is `max(|x|, γ)⁻²`. -/
noncomputable def rho (γ u : ℝ) : ℝ := (max u (γ ^ 2))⁻¹

/-- `u ↦ u·max(√u, γ)⁻²`: the functional calculus of `b^*b` and `bb^*` for
`b = a·max(|a|, γ)⁻¹`. -/
noncomputable def hgt (γ u : ℝ) : ℝ := phi γ u * phi γ u * u

/-- `v ↦ max(√v − β, 0)`. -/
noncomputable def cut (β v : ℝ) : ℝ := max (Real.sqrt v - β) 0

/-- `u ↦ φ_γ(u)·cut_β(hgt γ u)·φ_β(hgt γ u)`. -/
noncomputable def lft (γ β u : ℝ) : ℝ := phi γ u * (cut β (hgt γ u) * phi β (hgt γ u))

/-- `u ↦ max(γ, (√u − γβ)/(1 − β))`. -/
noncomputable def mult (γ β u : ℝ) : ℝ := max γ ((Real.sqrt u - γ * β) / (1 - β))

theorem max_sqrt_pos {γ : ℝ} (hγ : 0 < γ) (u : ℝ) : 0 < max (Real.sqrt u) γ :=
  lt_of_lt_of_le hγ (le_max_right _ _)

theorem max_sq_pos {γ : ℝ} (hγ : 0 < γ) (u : ℝ) : 0 < max u (γ ^ 2) :=
  lt_of_lt_of_le (by positivity) (le_max_right _ _)

theorem phi_pos {γ : ℝ} (hγ : 0 < γ) (u : ℝ) : 0 < phi γ u :=
  inv_pos.mpr (max_sqrt_pos hγ u)

theorem rho_pos {γ : ℝ} (hγ : 0 < γ) (u : ℝ) : 0 < rho γ u :=
  inv_pos.mpr (max_sq_pos hγ u)

theorem continuous_phi {γ : ℝ} (hγ : 0 < γ) : Continuous (phi γ) :=
  (Real.continuous_sqrt.max continuous_const).inv₀ fun u => (max_sqrt_pos hγ u).ne'

theorem continuous_rho {γ : ℝ} (hγ : 0 < γ) : Continuous (rho γ) :=
  (continuous_id.max continuous_const).inv₀ fun u => (max_sq_pos hγ u).ne'

theorem continuous_hgt {γ : ℝ} (hγ : 0 < γ) : Continuous (hgt γ) :=
  ((continuous_phi hγ).mul (continuous_phi hγ)).mul continuous_id

theorem continuous_cut (β : ℝ) : Continuous (cut β) :=
  (Real.continuous_sqrt.sub continuous_const).max continuous_const

theorem continuous_lft {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 < β) : Continuous (lft γ β) :=
  (continuous_phi hγ).mul (((continuous_cut β).comp (continuous_hgt hγ)).mul
    ((continuous_phi hβ).comp (continuous_hgt hγ)))

theorem continuous_mult (γ β : ℝ) : Continuous (mult γ β) :=
  continuous_const.max ((Real.continuous_sqrt.sub continuous_const).div_const _)

theorem rho_mul_self_eq_one {γ u : ℝ} (hγ : 0 < γ) (hu : γ ^ 2 < u) : rho γ u * u = 1 := by
  rw [rho, max_eq_left hu.le, inv_mul_cancel₀ (lt_trans (by positivity) hu).ne']

theorem rho_mul_mul_rho_le {γ u : ℝ} (hγ : 0 < γ) (hu : 0 ≤ u) :
    rho γ u * u * rho γ u ≤ γ⁻¹ ^ 2 := by
  have hm := max_sq_pos hγ u
  have h1 : u ≤ max u (γ ^ 2) := le_max_left _ _
  have h2 : γ ^ 2 ≤ max u (γ ^ 2) := le_max_right _ _
  have hγ2 : 0 < γ ^ 2 := by positivity
  have key : u * γ ^ 2 ≤ max u (γ ^ 2) * max u (γ ^ 2) := mul_le_mul h1 h2 hγ2.le hm.le
  rw [rho, inv_pow, mul_comm (max u (γ ^ 2))⁻¹ u, mul_assoc, ← mul_inv, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos hm hm), inv_mul_eq_div, le_div_iff₀ hγ2]
  exact key

theorem phi_mul_mul_phi_le_one {γ u : ℝ} (hγ : 0 < γ) (hu : 0 ≤ u) :
    phi γ u * u * phi γ u ≤ 1 := by
  have hm := max_sqrt_pos hγ u
  have h1 : Real.sqrt u ≤ max (Real.sqrt u) γ := le_max_left _ _
  have key : u ≤ max (Real.sqrt u) γ * max (Real.sqrt u) γ := by
    have hs : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu
    have := mul_self_le_mul_self (Real.sqrt_nonneg u) h1
    rwa [hs] at this
  rw [phi, mul_comm (max (Real.sqrt u) γ)⁻¹ u, mul_assoc, ← mul_inv, ← div_eq_mul_inv,
    div_le_one (mul_pos hm hm)]
  exact key

theorem hgt_nonneg {γ u : ℝ} (hγ : 0 < γ) (hu : 0 ≤ u) : 0 ≤ hgt γ u :=
  mul_nonneg (mul_nonneg (phi_pos hγ u).le (phi_pos hγ u).le) hu

theorem hgt_le_one {γ u : ℝ} (hγ : 0 < γ) (hu : 0 ≤ u) : hgt γ u ≤ 1 := by
  rw [hgt, mul_right_comm]
  exact phi_mul_mul_phi_le_one hγ hu

theorem sqrt_hgt {γ u : ℝ} (hγ : 0 < γ) (hu : 0 ≤ u) :
    Real.sqrt (hgt γ u) = Real.sqrt u / max (Real.sqrt u) γ := by
  have hm := max_sqrt_pos hγ u
  have hs : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu
  have h : hgt γ u = (Real.sqrt u / max (Real.sqrt u) γ) *
      (Real.sqrt u / max (Real.sqrt u) γ) := by
    rw [hgt, phi, div_mul_div_comm, hs, div_eq_mul_inv, mul_inv]
    ring
  rw [h, Real.sqrt_mul_self (div_nonneg (Real.sqrt_nonneg u) hm.le)]

/-- **The pointwise estimate behind Corollary 4.**  For `u ≥ 0`,
`(1 − M(u)L(u))² u ≤ (γβ)²`; with `t = √u` it reads `min(t, γβ)² ≤ (γβ)²`. -/
theorem rordam_pointwise {γ β u : ℝ} (hγ : 0 < γ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hu : 0 ≤ u) :
    (1 - mult γ β u * lft γ β u) * u * (1 - mult γ β u * lft γ β u) ≤ (γ * β) ^ 2 := by
  obtain ⟨t, ht0, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ t * t = u :=
    ⟨Real.sqrt u, Real.sqrt_nonneg u, Real.mul_self_sqrt hu⟩
  have hst : Real.sqrt (t * t) = t := Real.sqrt_mul_self ht0
  have hsh : Real.sqrt (hgt γ (t * t)) = t / max t γ := by
    rw [sqrt_hgt hγ (mul_self_nonneg t), hst]
  have hγβ : γ * β < γ := by nlinarith
  have h1β : 0 < 1 - β := by linarith
  rcases le_or_gt t (γ * β) with hA | hA
  · have hmax : max t γ = γ := max_eq_right (by linarith)
    have hcut : cut β (hgt γ (t * t)) = 0 := by
      rw [cut, hsh, hmax]
      apply max_eq_right
      rw [sub_nonpos, div_le_iff₀ hγ]
      linarith [mul_comm β γ]
    have hL : lft γ β (t * t) = 0 := by rw [lft, hcut, zero_mul, mul_zero]
    rw [hL, mul_zero, sub_zero, one_mul, mul_one]
    nlinarith
  · have ht_pos : 0 < t := lt_of_le_of_lt (mul_pos hγ hβ0).le hA
    have hML : mult γ β (t * t) * lft γ β (t * t) = (t - γ * β) / t := by
      rcases le_or_gt t γ with hB | hB
      · have hmax : max t γ = γ := max_eq_right hB
        have hq : β ≤ t / γ := by
          rw [le_div_iff₀ hγ]
          linarith [mul_comm β γ]
        have hcut : cut β (hgt γ (t * t)) = t / γ - β := by
          rw [cut, hsh, hmax]
          exact max_eq_left (by linarith)
        have hphiβ : phi β (hgt γ (t * t)) = (t / γ)⁻¹ := by
          rw [phi, hsh, hmax, max_eq_left hq]
        have hphiγ : phi γ (t * t) = γ⁻¹ := by rw [phi, hst, hmax]
        have hmult : mult γ β (t * t) = γ := by
          rw [mult, hst]
          apply max_eq_left
          rw [div_le_iff₀ h1β]
          nlinarith
        rw [hmult, lft, hcut, hphiβ, hphiγ]
        first
          | (field_simp; ring)
          | field_simp
      · have hmax : max t γ = t := max_eq_left hB.le
        have htt : t / t = 1 := div_self ht_pos.ne'
        have hcut : cut β (hgt γ (t * t)) = 1 - β := by
          rw [cut, hsh, hmax, htt]
          exact max_eq_left h1β.le
        have hphiβ : phi β (hgt γ (t * t)) = 1 := by
          rw [phi, hsh, hmax, htt, max_eq_left hβ1.le, inv_one]
        have hphiγ : phi γ (t * t) = t⁻¹ := by rw [phi, hst, hmax]
        have hmult : mult γ β (t * t) = (t - γ * β) / (1 - β) := by
          rw [mult, hst]
          apply max_eq_right
          rw [le_div_iff₀ h1β]
          nlinarith
        rw [hmult, lft, hcut, hphiβ, hphiγ]
        first
          | (field_simp; ring)
          | field_simp
    rw [hML]
    have hval : (1 - (t - γ * β) / t) * (t * t) * (1 - (t - γ * β) / t) = (γ * β) ^ 2 := by
      first
        | (field_simp; ring)
        | field_simp
    rw [hval]

/-! ## Farah–Rørdam, Lemma 2 -/

variable {A : Type*} [CStarAlgebra A]

/-- **Farah–Rørdam, Lemma 2 (`n = 1`), in continuous functional calculus.**

If `z` is invertible and `‖x − z‖ < γ`, there is an invertible `s` with
`G(xx^*)·s = x·(G·φ_γ)(x^*x)` for every continuous `G` vanishing on `(−∞, γ²]`. -/
theorem exists_isUnit_cfc_mul_eq {x z : A} (hz : IsUnit z) {γ : ℝ} (hγ : 0 < γ)
    (hxz : ‖x - z‖ < γ) :
    ∃ s : A, IsUnit s ∧ ∀ G : ℝ → ℝ, Continuous G → (∀ u, u ≤ γ ^ 2 → G u = 0) →
      cfc G (x * star x) * s = x * cfc (fun u => G u * phi γ u) (star x * x) := by
  have hsa₁ : IsSelfAdjoint (star x * x) := IsSelfAdjoint.star_mul_self x
  have hρsa : IsSelfAdjoint (cfc (rho γ) (star x * x)) := cfc_predicate _ _
  set p : A := x * cfc (rho γ) (star x * x) with hpdef
  have hstar_p : star p = cfc (rho γ) (star x * x) * star x := by
    rw [hpdef, star_mul, hρsa.star_eq]
  have hpp : star p * p = cfc (fun u => rho γ u * u * rho γ u) (star x * x) := by
    rw [hstar_p, hpdef, mul_assoc, ← mul_assoc (star x) x, ← mul_assoc]
    exact cfc_mul_self_mul_cfc (star x * x) hsa₁ _ _ (continuous_rho hγ) (continuous_rho hγ)
  have hp_norm : ‖p‖ ≤ γ⁻¹ := by
    have h : ‖star p * p‖ ≤ γ⁻¹ ^ 2 := by
      rw [hpp]
      refine norm_cfc_le (by positivity) fun u hu => ?_
      have hu0 : 0 ≤ u := spectrum_star_mul_self_nonneg u hu
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (rho_pos hγ u).le hu0) (rho_pos hγ u).le)]
      exact rho_mul_mul_rho_le hγ hu0
    rw [CStarRing.norm_star_mul_self, sq] at h
    exact (mul_self_le_mul_self_iff (norm_nonneg p) (inv_pos.mpr hγ).le).mpr h
  set e : A := 1 + star p * (z - x) with hedef
  have he : IsUnit e := by
    have hlt : ‖-(star p * (z - x))‖ < 1 := by
      rw [norm_neg]
      calc ‖star p * (z - x)‖ ≤ ‖star p‖ * ‖z - x‖ := norm_mul_le _ _
        _ = ‖p‖ * ‖x - z‖ := by rw [norm_star, norm_sub_rev]
        _ < γ⁻¹ * γ := mul_lt_mul' hp_norm hxz (norm_nonneg _) (inv_pos.mpr hγ)
        _ = 1 := inv_mul_cancel₀ hγ.ne'
    have h := isUnit_one_sub_of_norm_lt_one hlt
    rwa [sub_neg_eq_add] at h
  have hΦ : IsUnit (cfc (phi γ) (star x * x)) :=
    (isUnit_cfc_iff (phi γ) (star x * x) (continuous_phi hγ).continuousOn hsa₁).mpr
      fun u _ => (phi_pos hγ u).ne'
  refine ⟨z * Ring.inverse e * cfc (phi γ) (star x * x), (hz.mul he.ringInverse).mul hΦ, ?_⟩
  intro G hG hGvan
  have hxp : x * star p = cfc (fun u => rho γ u * u) (x * star x) := by
    rw [hstar_p, ← mul_assoc]
    exact mul_cfc_star_mul_self_mul_star x (rho γ) (continuous_rho hγ)
  have ha : cfc G (x * star x) * (x * star p) = cfc G (x * star x) := by
    rw [hxp, ← cfc_mul G (fun u => rho γ u * u) (x * star x) hG.continuousOn
      ((continuous_rho hγ).mul continuous_id).continuousOn]
    refine cfc_congr fun u _ => ?_
    by_cases hu : u ≤ γ ^ 2
    · simp only [hGvan u hu, zero_mul]
    · push_neg at hu
      simp only [rho_mul_self_eq_one hγ hu, mul_one]
  have hb : cfc G (x * star x) * z = cfc G (x * star x) * x * e := by
    have h1 : cfc G (x * star x) * x * (star p * (z - x)) = cfc G (x * star x) * (z - x) := by
      rw [← mul_assoc, mul_assoc (cfc G (x * star x)) x (star p), ha]
    calc cfc G (x * star x) * z
        = cfc G (x * star x) * x + cfc G (x * star x) * (z - x) := by
          rw [← mul_add]
          congr 1
          abel
      _ = cfc G (x * star x) * x + cfc G (x * star x) * x * (star p * (z - x)) := by
          rw [h1]
      _ = cfc G (x * star x) * x * e := by rw [hedef, mul_add, mul_one]
  calc cfc G (x * star x) * (z * Ring.inverse e * cfc (phi γ) (star x * x))
      = cfc G (x * star x) * z * Ring.inverse e * cfc (phi γ) (star x * x) := by
        simp only [mul_assoc]
    _ = cfc G (x * star x) * x * (e * Ring.inverse e) * cfc (phi γ) (star x * x) := by
        rw [hb]
        simp only [mul_assoc]
    _ = x * cfc G (star x * x) * cfc (phi γ) (star x * x) := by
        rw [Ring.mul_inverse_cancel e he, mul_one, ← mul_cfc_star_mul_self x G hG]
    _ = x * cfc (fun u => G u * phi γ u) (star x * x) := by
        rw [mul_assoc, ← cfc_mul G (phi γ) (star x * x) hG.continuousOn
          (continuous_phi hγ).continuousOn]

/-! ## Rørdam's theorem -/

/-- **Rørdam, Ann. of Math. 128 (1988), Theorem 2.6**: if the invertible elements of
a unital C⋆-algebra are not dense, some element has norm one and distance one to
them. -/
theorem exists_norm_eq_one_distGL_eq_one (h : ¬ Dense (invertibles A)) :
    ∃ b : A, ‖b‖ = 1 ∧ distGL b = 1 := by
  obtain hA | hA := subsingleton_or_nontrivial A
  · exact absurd (dense_invertibles_iff.mpr fun x =>
      Metric.infDist_zero_of_mem (mem_invertibles.mpr (isUnit_of_subsingleton x))) h
  rw [dense_invertibles_iff, not_forall] at h
  obtain ⟨a, ha⟩ := h
  have hγ : 0 < distGL a := lt_of_le_of_ne (distGL_nonneg a) (Ne.symm ha)
  set γ : ℝ := distGL a with hγdef
  have hsa₁ : IsSelfAdjoint (star a * a) := IsSelfAdjoint.star_mul_self a
  have hsa₂ : IsSelfAdjoint (a * star a) := by
    simpa only [star_star] using IsSelfAdjoint.star_mul_self (star a)
  have hφsa : IsSelfAdjoint (cfc (phi γ) (star a * a)) := cfc_predicate _ _
  set b : A := a * cfc (phi γ) (star a * a) with hbdef
  have hbb : star b * b = cfc (hgt γ) (star a * a) := by
    rw [hbdef, star_mul, hφsa.star_eq, mul_assoc, ← mul_assoc (star a) a, ← mul_assoc,
      cfc_mul_self_mul_cfc (star a * a) hsa₁ _ _ (continuous_phi hγ) (continuous_phi hγ)]
    exact cfc_congr fun u _ => by simp only [hgt]; ring
  have hbbs : b * star b = cfc (hgt γ) (a * star a) := by
    rw [hbdef, star_mul, hφsa.star_eq, mul_assoc, ← mul_assoc (cfc (phi γ) (star a * a)),
      ← cfc_mul (phi γ) (phi γ) (star a * a) (continuous_phi hγ).continuousOn
        (continuous_phi hγ).continuousOn, ← mul_assoc,
      mul_cfc_star_mul_self_mul_star a _ ((continuous_phi hγ).mul (continuous_phi hγ))]
    rfl
  have hb_norm : ‖b‖ ≤ 1 := by
    have h : ‖star b * b‖ ≤ 1 := by
      rw [hbb]
      refine norm_cfc_le zero_le_one fun u hu => ?_
      have hu0 : 0 ≤ u := spectrum_star_mul_self_nonneg u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (hgt_nonneg hγ hu0)]
      exact hgt_le_one hγ hu0
    rw [CStarRing.norm_star_mul_self] at h
    exact (mul_self_le_mul_self_iff (norm_nonneg b) zero_le_one).mpr (by rwa [mul_one])
  have hdb_le : distGL b ≤ 1 := (distGL_le_norm b).trans hb_norm
  suffices hdb : 1 ≤ distGL b by
    have hd1 : distGL b = 1 := le_antisymm hdb_le hdb
    have hn := distGL_le_norm b
    rw [hd1] at hn
    exact ⟨b, le_antisymm hb_norm hn, hd1⟩
  by_contra hlt
  push_neg at hlt
  have hdb0 := distGL_nonneg b
  set β : ℝ := (distGL b + 1) / 2 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hβb : distGL b < β := by rw [hβdef]; linarith
  obtain ⟨z, hz, hbz⟩ := exists_isUnit_norm_sub_lt hβb
  obtain ⟨s, hs, hsG⟩ := exists_isUnit_cfc_mul_eq hz hβ0 hbz
  have hGv : ∀ v, v ≤ β ^ 2 → cut β v = 0 := by
    intro v hv
    have h1 : Real.sqrt v ≤ β :=
      calc Real.sqrt v ≤ Real.sqrt (β ^ 2) := Real.sqrt_le_sqrt hv
        _ = β := Real.sqrt_sq hβ0.le
    exact max_eq_right (by linarith)
  have hkey := hsG (cut β) (continuous_cut β) hGv
  rw [hbbs, hbb, ← cfc_comp (cut β) (hgt γ) (a * star a) hsa₂
      (continuous_cut β).continuousOn (continuous_hgt hγ).continuousOn,
    ← cfc_comp (fun u => cut β u * phi β u) (hgt γ) (star a * a) hsa₁
      ((continuous_cut β).mul (continuous_phi hβ0)).continuousOn
      (continuous_hgt hγ).continuousOn,
    hbdef, mul_assoc,
    ← cfc_mul (phi γ) ((fun u => cut β u * phi β u) ∘ hgt γ) (star a * a)
      (continuous_phi hγ).continuousOn
      (((continuous_cut β).mul (continuous_phi hβ0)).comp (continuous_hgt hγ)).continuousOn]
    at hkey
  have hkey' : cfc (fun u => cut β (hgt γ u)) (a * star a) * s
      = a * cfc (lft γ β) (star a * a) := hkey
  set w : A := cfc (fun u => mult γ β u * cut β (hgt γ u)) (a * star a) * s with hwdef
  have hw_closure : w ∈ closure (invertibles A) := by
    refine nonneg_mul_mem_closure_invertibles (cfc_nonneg fun u _ => ?_) hs
    exact mul_nonneg (le_trans hγ.le (le_max_left _ _)) (le_max_right _ _)
  have hw_eq : w = a * cfc (fun u => mult γ β u * lft γ β u) (star a * a) := by
    rw [hwdef, cfc_mul (mult γ β) (fun u => cut β (hgt γ u)) (a * star a)
        (continuous_mult γ β).continuousOn
        ((continuous_cut β).comp (continuous_hgt hγ)).continuousOn,
      mul_assoc, hkey', ← mul_assoc, ← mul_cfc_star_mul_self a (mult γ β) (continuous_mult γ β),
      mul_assoc, ← cfc_mul (mult γ β) (lft γ β) (star a * a) (continuous_mult γ β).continuousOn
        (continuous_lft hγ hβ0).continuousOn]
  have hNc : Continuous fun u => 1 - mult γ β u * lft γ β u :=
    continuous_const.sub ((continuous_mult γ β).mul (continuous_lft hγ hβ0))
  have hdist : ‖a - w‖ ≤ γ * β := by
    rw [hw_eq]
    have hN : a - a * cfc (fun u => mult γ β u * lft γ β u) (star a * a)
        = a * cfc (fun u => 1 - mult γ β u * lft γ β u) (star a * a) := by
      rw [cfc_sub (fun _ => (1 : ℝ)) (fun u => mult γ β u * lft γ β u) (star a * a)
          continuousOn_const ((continuous_mult γ β).mul (continuous_lft hγ hβ0)).continuousOn,
        cfc_const_one ℝ (star a * a) hsa₁, mul_sub, mul_one]
    rw [hN]
    have hNsa : IsSelfAdjoint (cfc (fun u => 1 - mult γ β u * lft γ β u) (star a * a)) :=
      cfc_predicate _ _
    have hsq : star (a * cfc (fun u => 1 - mult γ β u * lft γ β u) (star a * a)) *
        (a * cfc (fun u => 1 - mult γ β u * lft γ β u) (star a * a))
        = cfc (fun u => (1 - mult γ β u * lft γ β u) * u * (1 - mult γ β u * lft γ β u))
            (star a * a) := by
      rw [star_mul, hNsa.star_eq, mul_assoc, ← mul_assoc (star a) a, ← mul_assoc]
      exact cfc_mul_self_mul_cfc (star a * a) hsa₁ _ _ hNc hNc
    have h2 : ‖star (a * cfc (fun u => 1 - mult γ β u * lft γ β u) (star a * a)) *
        (a * cfc (fun u => 1 - mult γ β u * lft γ β u) (star a * a))‖ ≤ (γ * β) ^ 2 := by
      rw [hsq]
      refine norm_cfc_le (by positivity) fun u hu => ?_
      have hu0 : 0 ≤ u := spectrum_star_mul_self_nonneg u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        nlinarith [mul_nonneg (mul_self_nonneg (1 - mult γ β u * lft γ β u)) hu0])]
      exact rordam_pointwise hγ hβ0 hβ1 hu0
    rw [CStarRing.norm_star_mul_self, sq] at h2
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (mul_pos hγ hβ0).le).mpr h2
  have hcontra : γ ≤ γ * β :=
    calc γ = distGL a := hγdef
      _ ≤ ‖a - w‖ := distGL_le_norm_sub_of_mem_closure hw_closure
      _ ≤ γ * β := hdist
  nlinarith

end RordamDistanceOne
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.RordamDistanceOne.rordam_pointwise
#audit_axioms GroupApproximation.RordamDistanceOne.exists_isUnit_cfc_mul_eq
#audit_axioms GroupApproximation.RordamDistanceOne.exists_norm_eq_one_distGL_eq_one
