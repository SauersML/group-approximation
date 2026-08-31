import GroupApproximation.Analysis.CalkinCStarAlgebra
import GroupApproximation.Analysis.ShiftIsometry

/-!
# Concrete Fock-space shifts for the actual O₂ model

This is genuine operator-algebra infrastructure, not an abstract replacement
for the STW problem.  We use the full Fock Hilbert space over two letters,
`ℓ²(List Bool)`, and the two left-prefix shifts.  They are orthogonal
isometries.  Their range projections miss exactly the vacuum; after passing to
the Calkin algebra that rank-one defect vanishes, giving the Cuntz relation.

This file establishes the isometry and orthogonality half.  The Calkin Cuntz
relation is built in the next layer.
-/

namespace STW.Actual

open scoped ENNReal InnerProductSpace

noncomputable section

abbrev FockIndex := List Bool
abbrev FockSpace := lp (fun _ : FockIndex ↦ ℂ) 2

local instance : DecidableEq FockIndex := Classical.decEq FockIndex

/-- Prefix a binary word by `b`. -/
def prefixMap (b : Bool) : FockIndex → FockIndex := fun w ↦ b :: w

@[simp] theorem prefixMap_apply (b : Bool) (w : FockIndex) :
    prefixMap b w = b :: w := rfl

theorem prefixMap_injective (b : Bool) : Function.Injective (prefixMap b) := by
  intro x y h
  exact List.cons.inj h |>.2

/-- The two prefix ranges are disjoint. -/
theorem prefixMap_ranges_disjoint {b c : Bool} (hbc : b ≠ c) (x y : FockIndex) :
    prefixMap b x ≠ prefixMap c y := by
  intro h
  exact hbc (List.cons.inj h |>.1)

/-- Extension by zero along a prefix embedding preserves square summability. -/
theorem memℓp_prefixExtend (b : Bool) (f : FockSpace) :
    Memℓp (Function.extend (prefixMap b) (⇑f) 0) 2 := by
  apply memℓp_gen
  have ht : (2 : ℝ≥0∞).toReal ≠ 0 := by simp
  have hnorm : (fun y : FockIndex ↦
      ‖Function.extend (prefixMap b) (⇑f) 0 y‖ ^ (2 : ℝ≥0∞).toReal)
      = Function.extend (prefixMap b)
          (fun x ↦ ‖f x‖ ^ (2 : ℝ≥0∞).toReal) 0 := by
    funext y
    rcases em (∃ x, prefixMap b x = y) with ⟨x, rfl⟩ | hy
    · rw [(prefixMap_injective b).extend_apply,
        (prefixMap_injective b).extend_apply]
    · rw [Function.extend_apply' _ _ _ hy, Function.extend_apply' _ _ _ hy]
      simp only [Pi.zero_apply, norm_zero]
      rw [Real.zero_rpow ht]
  rw [hnorm]
  have hcomp : (Function.extend (prefixMap b)
        (fun x ↦ ‖f x‖ ^ (2 : ℝ≥0∞).toReal) 0) ∘ prefixMap b
      = fun x ↦ ‖f x‖ ^ (2 : ℝ≥0∞).toReal :=
    funext fun x ↦ (prefixMap_injective b).extend_apply _ _ _
  refine ((prefixMap_injective b).summable_iff (fun y hy ↦ ?_)).mp ?_
  · rw [Function.extend_apply' _ _ _ (by simpa using hy)]
    rfl
  · rw [hcomp]
    exact (memℓp_gen_iff (by norm_num)).1 (lp.memℓp f)

/-- The left-prefix shift on Fock space. -/
def prefixFun (b : Bool) (f : FockSpace) : FockSpace :=
  ⟨Function.extend (prefixMap b) (⇑f) 0, memℓp_prefixExtend b f⟩

@[simp] theorem prefixFun_apply_prefix (b : Bool) (f : FockSpace) (w : FockIndex) :
    prefixFun b f (prefixMap b w) = f w :=
  (prefixMap_injective b).extend_apply _ _ _

@[simp] theorem prefixFun_apply_off (b : Bool) (f : FockSpace) {y : FockIndex}
    (hy : ¬ ∃ x, prefixMap b x = y) : prefixFun b f y = 0 := by
  show Function.extend (prefixMap b) (⇑f) 0 y = 0
  rw [Function.extend_apply' _ _ _ hy]
  rfl

/-- Prefixing is linear. -/
def prefixLinear (b : Bool) : FockSpace →ₗ[ℂ] FockSpace where
  toFun := prefixFun b
  map_add' f g := by
    apply lp.ext
    funext y
    rcases em (∃ x, prefixMap b x = y) with ⟨x, rfl⟩ | hy
    · simp only [lp.coeFn_add, Pi.add_apply, prefixFun_apply_prefix]
    · simp only [lp.coeFn_add, Pi.add_apply, prefixFun_apply_off _ _ hy, add_zero]
  map_smul' c f := by
    apply lp.ext
    funext y
    rcases em (∃ x, prefixMap b x = y) with ⟨x, rfl⟩ | hy
    · simp only [lp.coeFn_smul, Pi.smul_apply, prefixFun_apply_prefix,
        RingHom.id_apply]
    · simp only [lp.coeFn_smul, Pi.smul_apply, prefixFun_apply_off _ _ hy,
        smul_zero, RingHom.id_apply]

@[simp] theorem prefixLinear_apply (b : Bool) (f : FockSpace) :
    prefixLinear b f = prefixFun b f := rfl

/-- Each prefix shift preserves the Hilbert inner product. -/
theorem inner_prefixFun (b : Bool) (f g : FockSpace) :
    ⟪prefixFun b f, prefixFun b g⟫_ℂ = ⟪f, g⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hfun : (fun y : FockIndex ↦ ⟪prefixFun b f y, prefixFun b g y⟫_ℂ)
      = Function.extend (prefixMap b) (fun x ↦ ⟪f x, g x⟫_ℂ) 0 := by
    funext y
    rcases em (∃ x, prefixMap b x = y) with ⟨x, rfl⟩ | hy
    · rw [(prefixMap_injective b).extend_apply, prefixFun_apply_prefix,
        prefixFun_apply_prefix]
    · rw [Function.extend_apply' _ _ _ hy, prefixFun_apply_off _ _ hy,
        prefixFun_apply_off _ _ hy]
      simp
  rw [hfun]
  exact tsum_eq_tsum_of_hasSum_iff_hasSum fun {a} ↦
    hasSum_extend_zero (prefixMap_injective b)

/-- Distinct prefix ranges are orthogonal. -/
theorem inner_prefixFun_of_ne {b c : Bool} (hbc : b ≠ c) (f g : FockSpace) :
    ⟪prefixFun b f, prefixFun c g⟫_ℂ = 0 := by
  rw [lp.inner_eq_tsum]
  have hz : (fun y : FockIndex ↦ ⟪prefixFun b f y, prefixFun c g y⟫_ℂ) = 0 := by
    funext y
    rcases em (∃ x, prefixMap b x = y) with ⟨x, rfl⟩ | hb
    · have hc : ¬ ∃ z, prefixMap c z = prefixMap b x := by
        rintro ⟨z, hz⟩
        exact prefixMap_ranges_disjoint hbc x z hz.symm
      rw [prefixFun_apply_prefix, prefixFun_apply_off _ _ hc]
      simp
    · rw [prefixFun_apply_off _ _ hb]
      simp
  rw [hz]
  simp

/-- The prefix shift as a linear isometry. -/
def prefixIsometry (b : Bool) : FockSpace →ₗᵢ[ℂ] FockSpace :=
  (prefixLinear b).isometryOfInner fun f g ↦ inner_prefixFun b f g

/-- The prefix shift as an element of `B(FockSpace)`. -/
def prefixOp (b : Bool) : FockSpace →L[ℂ] FockSpace :=
  (prefixIsometry b).toContinuousLinearMap

/-- Each prefix operator is an isometry: `S_b* S_b = 1`. -/
theorem prefixOp_star_mul_self (b : Bool) :
    star (prefixOp b) * prefixOp b = 1 := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp
    fun f g ↦ inner_prefixFun b f g

/-- Distinct prefix operators have orthogonal ranges: `S_b* S_c = 0`. -/
theorem prefixOp_star_mul_of_ne {b c : Bool} (hbc : b ≠ c) :
    star (prefixOp b) * prefixOp c = 0 := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  ext f
  let z : FockSpace := ContinuousLinearMap.adjoint (prefixOp b) (prefixOp c f)
  change z = 0
  apply inner_self_eq_zero.mp
  have hadj : ⟪z, z⟫_ℂ = ⟪prefixOp c f, prefixOp b z⟫_ℂ := by
    exact (ContinuousLinearMap.adjoint_inner_left (prefixOp b) z (prefixOp c f)).symm
  rw [hadj]
  exact inner_prefixFun_of_ne hbc.symm f z

@[simp] theorem prefixOp_star_mul_false_true :
    star (prefixOp false) * prefixOp true = 0 :=
  prefixOp_star_mul_of_ne (by decide)

@[simp] theorem prefixOp_star_mul_true_false :
    star (prefixOp true) * prefixOp false = 0 :=
  prefixOp_star_mul_of_ne (by decide)

end

end STW.Actual
