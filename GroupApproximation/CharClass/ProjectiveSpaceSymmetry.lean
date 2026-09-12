import GroupApproximation.CharClass.ProjectiveSpaceChart

/-!
# `ℂP^d` is path connected

`H^0(ℂP^d; F₂)` is a line, and that is what supplies the degree-zero input to the
Mayer–Vietoris induction of `CharClass/ProjectiveSpaceCohomology.lean`.  Lane
`cc-cohom-api`'s `cohZeroEquiv` delivers it for any nonempty path-connected
space, so what is needed here is path-connectedness of the projection model.

The proof is a straight segment, and the only subtlety is that a segment between
two unit vectors can pass through the origin — precisely when they are negative
real multiples of one another.  Over `ℂ` that is avoidable for free: rescaling
`y` by a unit scalar does not move the line it spans, so `y` may first be rotated
until `⟨x, y⟩` is a nonnegative real, after which

```text
⟨x, (1-t)x + t y⟩ = (1-t) + t⟨x, y⟩ > 0        for 0 ≤ t < 1
```

and the segment cannot vanish.  No inner-product-space structure is needed: the
Hermitian form is written out as a sum, and the three facts used about it are
proved directly.

## Main declarations

* `herm` — the Hermitian form `∑ conj(xᵢ) yᵢ`, and `unitPhase` — the unit scalar
  rotating a complex number onto the nonnegative reals.
* `segVec`, `segMat` — the segment and the rank-one projection onto it, the
  latter written through `rankOneProj_normalize` so that no square root appears
  and continuity is entrywise division by a nonvanishing denominator.
* `joined_of_unitVectors` — any two points of `ℂP^d` are joined by a path.
* `instPathConnectedSpaceCP` — the instance `cohZeroEquiv` consumes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open GroupApproximation.STW59

namespace CPn

noncomputable section

variable {d : ℕ}

/-! ## 1. The Hermitian form -/

/-- The Hermitian form `⟨x, y⟩ = ∑ conj(xᵢ) yᵢ`, linear in the second argument. -/
def herm {n : Type*} [Fintype n] (x y : n → ℂ) : ℂ := ∑ i, star (x i) * y i

theorem herm_self {n : Type*} [Fintype n] {x : n → ℂ} (hx : x ∈ unitVectors n) :
    herm x x = 1 :=
  sum_star_mul_self hx

@[simp] theorem herm_zero_right {n : Type*} [Fintype n] (x : n → ℂ) : herm x 0 = 0 := by
  simp [herm]

/-! ## 2. Rotating onto the nonnegative reals -/

/-- A unit complex number carrying `c` to `‖c‖`. -/
def unitPhase (c : ℂ) : ℂ := if c = 0 then 1 else ((‖c‖ : ℝ) : ℂ) / c

theorem norm_unitPhase (c : ℂ) : ‖unitPhase c‖ = 1 := by
  unfold unitPhase
  split_ifs with hc
  · simp
  · rw [norm_div, Complex.norm_of_nonneg (norm_nonneg c)]
    exact div_self (norm_ne_zero_iff.mpr hc)

theorem unitPhase_mul (c : ℂ) : unitPhase c * c = ((‖c‖ : ℝ) : ℂ) := by
  unfold unitPhase
  split_ifs with hc
  · rw [hc]; simp
  · field_simp

/-! ## 3. Unit vectors and rescaling -/

theorem smul_mem_unitVectors {n : Type*} [Fintype n] {c : ℂ} (hc : ‖c‖ = 1)
    {y : n → ℂ} (hy : y ∈ unitVectors n) : (fun a => c * y a) ∈ unitVectors n := by
  rw [mem_unitVectors_iff]
  have hterm : ∀ a : n, ‖c * y a‖ ^ 2 = ‖y a‖ ^ 2 := by
    intro a
    rw [norm_mul, hc, one_mul]
  rw [Finset.sum_congr rfl fun a _ => hterm a]
  exact mem_unitVectors_iff.mp hy

theorem rankOneProj_smul_of_norm_one {n : Type*} [Fintype n] {c : ℂ} (hc : ‖c‖ = 1)
    (y : n → ℂ) : rankOneProj (fun a => c * y a) = rankOneProj y := by
  have hcc : c * star c = 1 := by
    rw [mul_star_self_eq_normSq, hc]
    norm_num
  funext a b
  simp only [rankOneProj_apply, star_mul']
  calc c * y a * (star c * star (y b)) = c * star c * (y a * star (y b)) := by ring
    _ = y a * star (y b) := by rw [hcc, one_mul]

/-! ## 4. The segment -/

/-- The straight segment from `x` to `y`. -/
def segVec (x y : Fin (d + 1) → ℂ) (t : ℝ) : Fin (d + 1) → ℂ :=
  fun a => ((1 - t : ℝ) : ℂ) * x a + ((t : ℝ) : ℂ) * y a

@[simp] theorem segVec_zero (x y : Fin (d + 1) → ℂ) : segVec x y 0 = x := by
  funext a
  simp [segVec]

@[simp] theorem segVec_one (x y : Fin (d + 1) → ℂ) : segVec x y 1 = y := by
  funext a
  simp [segVec]

theorem herm_segVec (x y : Fin (d + 1) → ℂ) (t : ℝ) :
    herm x (segVec x y t)
      = ((1 - t : ℝ) : ℂ) * herm x x + ((t : ℝ) : ℂ) * herm x y := by
  simp only [herm, segVec, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The segment misses the origin.**  With `⟨x, y⟩` a nonnegative real and `x`,
`y` of unit length, `(1-t)x + ty` is never zero on `[0, 1]`. -/
theorem segVec_ne_zero {x y : Fin (d + 1) → ℂ}
    (hx : x ∈ unitVectors (Fin (d + 1))) (hy : y ∈ unitVectors (Fin (d + 1)))
    {s : ℝ} (hs : 0 ≤ s) (hxy : herm x y = ((s : ℝ) : ℂ))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : segVec x y t ≠ 0 := by
  intro hzero
  have hform : ((1 - t : ℝ) : ℂ) * 1 + ((t : ℝ) : ℂ) * ((s : ℝ) : ℂ) = 0 := by
    have h := herm_segVec x y t
    rw [hzero, herm_zero_right, herm_self hx, hxy] at h
    exact h.symm
  have hre : (1 - t) + t * s = 0 := by
    have h := congrArg Complex.re hform
    simpa using h
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · -- `t = 1`: the segment is `y`, which is a unit vector
    have hy0 : y = 0 := by
      rw [← segVec_one x y, ← h1]
      exact hzero
    have := mem_unitVectors_iff.mp hy
    rw [hy0] at this
    simp at this
  · nlinarith [mul_nonneg ht0 hs]

/-! ## 5. The path -/

/-- The rank-one projection onto the segment, written without a square root: this
is `rankOneProj (normalize (segVec x y t))` by `rankOneProj_normalize`, and in
this form its continuity is entrywise division by a nonvanishing denominator. -/
def segMat (x y : Fin (d + 1) → ℂ) (t : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun a b => segVec x y t a * star (segVec x y t b) / ((sqNorm (segVec x y t) : ℝ) : ℂ)

theorem sqNorm_ne_zero_of_ne_zero {n : Type*} [Fintype n] {u : n → ℂ} (hu : u ≠ 0) :
    sqNorm u ≠ 0 := by
  intro h
  refine hu (funext fun i => ?_)
  have hnonneg : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ ‖u j‖ ^ 2 := fun j _ => by positivity
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h i (Finset.mem_univ i)
  have : ‖u i‖ = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi
    exact this
  simpa using this

theorem segMat_eq {x y : Fin (d + 1) → ℂ} {t : ℝ} (hne : sqNorm (segVec x y t) ≠ 0) :
    segMat x y t = rankOneProj (normalize (segVec x y t)) := by
  funext a b
  exact (rankOneProj_normalize hne a b).symm

theorem segMat_mem {x y : Fin (d + 1) → ℂ} {t : ℝ} (hne : sqNorm (segVec x y t) ≠ 0) :
    segMat x y t ∈ cpSet d := by
  rw [segMat_eq hne]
  exact rankOneProj_mem_cpSet (normalize_mem hne)

theorem normalize_of_unit {n : Type*} [Fintype n] {x : n → ℂ} (hx : x ∈ unitVectors n) :
    normalize x = x := by
  funext a
  have h1 : sqNorm x = 1 := mem_unitVectors_iff.mp hx
  rw [normalize, h1, Real.sqrt_one]
  simp

theorem continuous_sqNorm {n : Type*} [Fintype n] : Continuous (sqNorm : (n → ℂ) → ℝ) :=
  continuous_finsetSum _ fun i _ => ((continuous_apply i).norm).pow 2

theorem continuous_segVec_apply (x y : Fin (d + 1) → ℂ) (a : Fin (d + 1)) :
    Continuous fun t : ℝ => segVec x y t a := by
  unfold segVec
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
      continuous_const).add (Complex.continuous_ofReal.mul continuous_const)

theorem continuous_segVec (x y : Fin (d + 1) → ℂ) :
    Continuous fun t : ℝ => segVec x y t :=
  continuous_pi fun a => continuous_segVec_apply x y a

/-- **Any two points of `ℂP^d` are joined by a path.** -/
theorem joined_rankOneProj {x y : Fin (d + 1) → ℂ}
    (hx : x ∈ unitVectors (Fin (d + 1))) (hy : y ∈ unitVectors (Fin (d + 1))) :
    Joined (⟨rankOneProj x, rankOneProj_mem_cpSet hx⟩ : CP d)
      ⟨rankOneProj y, rankOneProj_mem_cpSet hy⟩ := by
  set c : ℂ := unitPhase (herm x y) with hc
  set y' : Fin (d + 1) → ℂ := fun a => c * y a with hy'
  have hcnorm : ‖c‖ = 1 := norm_unitPhase _
  have hy'unit : y' ∈ unitVectors (Fin (d + 1)) := smul_mem_unitVectors hcnorm hy
  have hxy' : herm x y' = ((‖herm x y‖ : ℝ) : ℂ) := by
    have : herm x y' = c * herm x y := by
      simp only [herm, hy', Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hc, unitPhase_mul]
  have hne : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → sqNorm (segVec x y' t) ≠ 0 := fun t ht0 ht1 =>
    sqNorm_ne_zero_of_ne_zero
      (segVec_ne_zero hx hy'unit (norm_nonneg (herm x y)) hxy' ht0 ht1)
  have hcont : Continuous fun t : unitInterval =>
      (⟨segMat x y' (t : ℝ), segMat_mem (hne (t : ℝ) t.2.1 t.2.2)⟩ : CP d) := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun a b => ?_
    refine Continuous.div ?_ ?_ ?_
    · exact ((continuous_segVec_apply x y' a).comp continuous_subtype_val).mul
        (((continuous_segVec_apply x y' b).comp continuous_subtype_val).star)
    · exact Complex.continuous_ofReal.comp
        ((continuous_sqNorm.comp (continuous_segVec x y')).comp continuous_subtype_val)
    · intro t
      simpa using (Complex.ofReal_ne_zero).mpr (hne (t : ℝ) t.2.1 t.2.2)
  refine ⟨⟨⟨_, hcont⟩, ?_, ?_⟩⟩
  · refine Subtype.ext ?_
    show segMat x y' ((0 : unitInterval) : ℝ) = rankOneProj x
    rw [segMat_eq (hne _ (by norm_num) (by norm_num))]
    show rankOneProj (normalize (segVec x y' (0 : ℝ))) = rankOneProj x
    rw [segVec_zero, normalize_of_unit hx]
  · refine Subtype.ext ?_
    show segMat x y' ((1 : unitInterval) : ℝ) = rankOneProj y
    rw [segMat_eq (hne _ (by norm_num) (by norm_num))]
    show rankOneProj (normalize (segVec x y' (1 : ℝ))) = rankOneProj y
    rw [segVec_one, normalize_of_unit hy'unit, hy']
    exact rankOneProj_smul_of_norm_one hcnorm y

/-- **`ℂP^d` is path connected.**  This is what `cc-cohom-api`'s `cohZeroEquiv`
needs in order to give `H^0(ℂP^d; F₂) ≃ₗ F₂`. -/
instance instPathConnectedSpaceCP (d : ℕ) : PathConnectedSpace (CP d) where
  nonempty := CP.instNonempty d
  joined z w := by
    obtain ⟨x, hx, hzx⟩ :=
      eq_rankOneProj_of_trace_one (isStarProjection_of_mem_cpSet z.2) (trace_of_mem_cpSet z.2)
    obtain ⟨y, hy, hwy⟩ :=
      eq_rankOneProj_of_trace_one (isStarProjection_of_mem_cpSet w.2) (trace_of_mem_cpSet w.2)
    have hz : z = (⟨rankOneProj x, rankOneProj_mem_cpSet hx⟩ : CP d) := Subtype.ext hzx
    have hw : w = (⟨rankOneProj y, rankOneProj_mem_cpSet hy⟩ : CP d) := Subtype.ext hwy
    rw [hz, hw]
    exact joined_rankOneProj hx hy

end

end CPn

end CharClass
end GroupApproximation
