import GroupApproximation.CharClass.ProjectiveSpaceSymmetry

/-!
# `ℂP^d` is homogeneous

Lane `cc-thom`'s punctured-product recursion deletes the zero of a section, which
is not the base point, so it needs `ℂP^{d+1} ∖ {z} ≃ ℂP^{d+1} ∖ {basePoint}` for
an arbitrary `z`.  That is one homeomorphism of `ℂP^{d+1}` carrying `z` to the
base point, and this file builds it.

The unitary group acts by `q ↦ u q uᴴ`, which preserves self-adjointness,
idempotence and the trace, so it acts on the projection model; and every point of
`ℂP^{d+1}` is `x xᴴ` for a unit vector `x`, with `u (x xᴴ) uᴴ = (ux)(ux)ᴴ`.  So
everything reduces to a unitary carrying `x` to a unit multiple of the first
basis vector, and a **Householder reflection** provides one in closed form:

```text
u := 1 - (2 / ‖v‖²) • v vᴴ,      v := x - y',
```

where `y'` is the first basis vector rotated so that `⟨x, y'⟩` is a nonnegative
real — the same rotation used for path-connectedness in
`CharClass/ProjectiveSpaceSymmetry.lean`.  Then `u` is self-adjoint with `u² = 1`,
hence unitary, and `u x = y'` because `2⟨v, x⟩ / ‖v‖² = 1`.

No inner-product-space structure and no orthonormal-basis extension is used; the
route through `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` would
drag in `EuclideanSpace ℂ (Fin (d+2))` and a transport of the norm, which is more
work than the whole statement.

## Main declarations

* `conj_rankOneProj` — `a (x xᴴ) aᴴ = (ax)(ax)ᴴ`.
* `conjHomeo` — conjugation by a unitary, as a self-homeomorphism of `ℂP^d`.
* `houseMat` — the Householder reflection, self-adjoint and involutive.
* `exists_homeomorph_mapsTo_basePoint` — the statement `cc-thom` consumes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open GroupApproximation.STW59
open scoped Matrix

namespace CPn

noncomputable section

variable {d : ℕ}

/-! ## 1. More of the Hermitian form -/

theorem herm_conj {n : Type*} [Fintype n] (x y : n → ℂ) : herm y x = star (herm x y) := by
  simp only [herm, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_sub_left {n : Type*} [Fintype n] (x y z : n → ℂ) :
    herm (fun i => x i - y i) z = herm x z - herm y z := by
  simp only [herm, ← Finset.sum_sub_distrib, star_sub]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_sub_right {n : Type*} [Fintype n] (x y z : n → ℂ) :
    herm x (fun i => y i - z i) = herm x y - herm x z := by
  simp only [herm, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Hermitian form of a vector with itself is its squared norm. -/
theorem herm_self_eq_sqNorm {n : Type*} [Fintype n] (x : n → ℂ) :
    herm x x = ((sqNorm x : ℝ) : ℂ) := by
  simp only [herm, sqNorm, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => star_mul_self_eq_normSq (x i)

/-! ## 2. Conjugation acts on the projection model -/

theorem conj_rankOneProj {n : Type*} [Fintype n] (a : Matrix n n ℂ) (x : n → ℂ) :
    a * rankOneProj x * aᴴ = rankOneProj (a *ᵥ x) := by
  funext i j
  have hL : (a * rankOneProj x * aᴴ) i j
      = ∑ l, (∑ k, a i k * (x k * star (x l))) * star (a j l) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rankOneProj_apply]
  have hR : rankOneProj (a *ᵥ x) i j
      = (∑ k, a i k * x k) * ∑ l, star (a j l) * star (x l) := by
    simp [rankOneProj_apply, Matrix.mulVec, dotProduct, star_sum, star_mul']
  rw [hL, hR, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem conj_mem_cpSet {u q : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hu : uᴴ * u = 1) (hq : q ∈ cpSet d) : u * q * uᴴ ∈ cpSet d := by
  obtain ⟨hqH, hqI, hqT⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hqH, mul_assoc]
  · calc u * q * uᴴ * (u * q * uᴴ) = u * q * (uᴴ * u) * q * uᴴ := by
          simp only [mul_assoc]
      _ = u * (q * q) * uᴴ := by rw [hu]; simp only [mul_assoc, one_mul]
      _ = u * q * uᴴ := by rw [hqI]
  · rw [Matrix.trace_mul_cycle, hu, one_mul]
    exact hqT

/-- Conjugation by a unitary, as a self-map of `ℂP^d`. -/
def conjMap (u : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (hu : uᴴ * u = 1) (z : CP d) : CP d :=
  ⟨u * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * uᴴ, conj_mem_cpSet hu z.2⟩

theorem continuous_conjMap (u : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (hu : uᴴ * u = 1) :
    Continuous (conjMap u hu) :=
  Continuous.subtype_mk
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

/-- **Conjugation by a unitary is a homeomorphism of `ℂP^d`.** -/
def conjHomeo (u : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (hu : uᴴ * u = 1)
    (huu : u * uᴴ = 1) : CP d ≃ₜ CP d where
  toFun := conjMap u hu
  invFun := conjMap uᴴ (by rwa [Matrix.conjTranspose_conjTranspose])
  left_inv z := by
    refine Subtype.ext ?_
    show uᴴ * (u * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * uᴴ) * uᴴᴴ = z
    rw [Matrix.conjTranspose_conjTranspose]
    calc uᴴ * (u * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * uᴴ) * u
        = (uᴴ * u) * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (uᴴ * u) := by
          simp only [mul_assoc]
      _ = z := by rw [hu]; simp
  right_inv z := by
    refine Subtype.ext ?_
    show u * (uᴴ * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * uᴴᴴ) * uᴴ = z
    rw [Matrix.conjTranspose_conjTranspose]
    calc u * (uᴴ * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * u) * uᴴ
        = (u * uᴴ) * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (u * uᴴ) := by
          simp only [mul_assoc]
      _ = z := by rw [huu]; simp
  continuous_toFun := continuous_conjMap u hu
  continuous_invFun := continuous_conjMap uᴴ _

/-! ## 3. The Householder reflection -/

theorem rankOneProj_mul_rankOneProj {n : Type*} [Fintype n] (v : n → ℂ) :
    rankOneProj v * rankOneProj v = ((sqNorm v : ℝ) : ℂ) • rankOneProj v := by
  funext i j
  rw [Matrix.mul_apply]
  simp only [rankOneProj_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← herm_self_eq_sqNorm]
  simp only [herm, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem rankOneProj_mulVec {n : Type*} [Fintype n] (v x : n → ℂ) :
    rankOneProj v *ᵥ x = fun i => herm v x * v i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rankOneProj_apply, herm, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The Householder reflection in the hyperplane orthogonal to `v`. -/
def houseMat (v : Fin (d + 1) → ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  1 - ((2 / sqNorm v : ℝ) : ℂ) • rankOneProj v

theorem conjTranspose_rankOneProj {n : Type*} (v : n → ℂ) :
    (rankOneProj v)ᴴ = rankOneProj v := by
  funext i j
  simp only [Matrix.conjTranspose_apply, rankOneProj_apply, star_mul', star_star]
  ring

theorem conjTranspose_ofReal_smul {n : Type*} (r : ℝ) (M : Matrix n n ℂ) :
    (((r : ℝ) : ℂ) • M)ᴴ = ((r : ℝ) : ℂ) • Mᴴ := by
  funext i j
  simp [Matrix.conjTranspose_apply, Matrix.smul_apply, star_mul', Complex.conj_ofReal]

theorem houseMat_conjTranspose (v : Fin (d + 1) → ℂ) : (houseMat v)ᴴ = houseMat v := by
  unfold houseMat
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, conjTranspose_ofReal_smul,
    conjTranspose_rankOneProj]

theorem houseMat_mul_self {v : Fin (d + 1) → ℂ} (hv : sqNorm v ≠ 0) :
    houseMat v * houseMat v = 1 := by
  have hs : ((sqNorm v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  set c : ℂ := ((2 / sqNorm v : ℝ) : ℂ) with hcdef
  have hkey : c * c * ((sqNorm v : ℝ) : ℂ) = c + c := by
    rw [hcdef]
    push_cast
    field_simp
    ring
  show (1 - c • rankOneProj v) * (1 - c • rankOneProj v) = 1
  have hexpand : (1 - c • rankOneProj v) * (1 - c • rankOneProj v)
      = 1 - (c + c) • rankOneProj v + (c * c) • (rankOneProj v * rankOneProj v) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, add_smul]
    abel
  rw [hexpand, rankOneProj_mul_rankOneProj, smul_smul, hkey]
  abel

theorem houseMat_unitary {v : Fin (d + 1) → ℂ} (hv : sqNorm v ≠ 0) :
    (houseMat v)ᴴ * houseMat v = 1 := by
  rw [houseMat_conjTranspose]
  exact houseMat_mul_self hv

/-! ## 4. Homogeneity -/

/-- **Every point of `ℂP^{d}` is carried to the base point by a homeomorphism.** -/
theorem exists_homeomorph_mapsTo_basePoint (d : ℕ) (z : CP d) :
    ∃ e : CP d ≃ₜ CP d, e z = basePoint d := by
  obtain ⟨x, hx, hzx⟩ :=
    eq_rankOneProj_of_trace_one (isStarProjection_of_mem_cpSet z.2) (trace_of_mem_cpSet z.2)
  set y : Fin (d + 1) → ℂ := baseVec d with hydef
  have hy : y ∈ unitVectors (Fin (d + 1)) := basePoint_unit d
  set c : ℂ := unitPhase (herm x y) with hc
  set y' : Fin (d + 1) → ℂ := fun a => c * y a with hy'
  have hcnorm : ‖c‖ = 1 := norm_unitPhase _
  have hy'unit : y' ∈ unitVectors (Fin (d + 1)) := smul_mem_unitVectors hcnorm hy
  have hxy' : herm x y' = ((‖herm x y‖ : ℝ) : ℂ) := by
    have h : herm x y' = c * herm x y := by
      simp only [herm, hy', Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, hc, unitPhase_mul]
  set r : ℝ := ‖herm x y‖ with hr
  set v : Fin (d + 1) → ℂ := fun a => x a - y' a with hv
  by_cases hzero : sqNorm v = 0
  · -- `x = y'`, so `z` is already the base point
    refine ⟨Homeomorph.refl _, ?_⟩
    have hvz : v = 0 := by
      by_contra hne
      exact sqNorm_ne_zero_of_ne_zero hne hzero
    have hxy : x = y' := by
      funext a
      have ha : x a - y' a = 0 := congrFun hvz a
      exact sub_eq_zero.mp ha
    show z = basePoint d
    refine Subtype.ext ?_
    rw [hzx, hxy, hy']
    show rankOneProj (fun a => c * y a) = (basePoint d : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    rw [rankOneProj_smul_of_norm_one hcnorm, hydef]
    rfl
  · -- the Householder reflection carries `x` to `y'`
    have hsv : ((sqNorm v : ℝ) : ℂ) = 2 - 2 * ((r : ℝ) : ℂ) := by
      have h := herm_self_eq_sqNorm v
      rw [← h, hv, herm_sub_left, herm_sub_right, herm_sub_right, herm_self hx,
        herm_self hy'unit, hxy', herm_conj x y', hxy']
      simp only [Complex.star_def, Complex.conj_ofReal]
      ring
    have hvx : herm v x = 1 - ((r : ℝ) : ℂ) := by
      rw [hv, herm_sub_left, herm_self hx, herm_conj x y', hxy']
      simp only [Complex.star_def, Complex.conj_ofReal]
    have hcoef : ((2 / sqNorm v : ℝ) : ℂ) * herm v x = 1 := by
      have hne : ((sqNorm v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hzero
      have h2 : ((2 / sqNorm v : ℝ) : ℂ) = 2 / ((sqNorm v : ℝ) : ℂ) := by push_cast; ring
      have h1r : (1 : ℂ) - ((r : ℝ) : ℂ) ≠ 0 := by
        intro hcon
        apply hne
        rw [hsv]
        linear_combination 2 * hcon
      rw [h2, hvx, hsv]
      field_simp
    have hmul : houseMat v *ᵥ x = y' := by
      have hstep : houseMat v *ᵥ x
          = fun i => x i - ((2 / sqNorm v : ℝ) : ℂ) * (herm v x * v i) := by
        funext i
        simp only [houseMat, Matrix.mulVec, dotProduct, Matrix.sub_apply,
          Matrix.smul_apply, Matrix.one_apply, rankOneProj_apply, smul_eq_mul, sub_mul,
          Finset.sum_sub_distrib, herm]
        congr 1
        · simp
        · rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      rw [hstep]
      funext i
      rw [← mul_assoc, hcoef, one_mul]
      show x i - v i = y' i
      rw [hv]
      ring
    refine ⟨conjHomeo (houseMat v) (houseMat_unitary hzero)
      (by rw [houseMat_conjTranspose]; exact houseMat_mul_self hzero), ?_⟩
    refine Subtype.ext ?_
    show houseMat v * (z : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) * (houseMat v)ᴴ
      = (basePoint d : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    rw [hzx, conj_rankOneProj, hmul, hy', rankOneProj_smul_of_norm_one hcnorm y, hydef]
    rfl

end

end CPn

end CharClass
end GroupApproximation
