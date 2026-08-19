import GroupApproximation.Analysis.GroupVonNeumannTrace
import GroupApproximation.Analysis.TracialStandardFormCommutation

/-!
# `L(G)` on `ℓ²(G)` is a tracial standard form

Fifth module of the `LI.06d` lane (`p:limits-trace`).
`Analysis/TracialStandardFormCommutation.lean` proves the commutation theorem
and the generation payoff for an abstract von Neumann algebra with a unit
cyclic separating tracial vector and a modular conjugation given as data.
This module supplies that data for the group von Neumann algebra: `ℓ²(G)` is
the standard form of `L(G)`, with the trace vector `δ₁` and the concrete
modular conjugation `(Jf)(x) = conj (f(x⁻¹))`.

* `modularJ` — the conjugation, with its `ℓ²` membership by the inversion
  reindexing.
* `star_coefficient` — the coefficient identity
  `(T⋆δ₁)(x) = conj ((Tδ₁)(x⁻¹))` for `T ∈ L(G)`, which is exactly the
  defining property `J(TΩ) = T⋆Ω`.
* `groupTracialConjugation` — the `TracialConjugation` structure.
* `isTracialStandardForm` — `δ₁` is a unit cyclic separating tracial vector:
  cyclicity by the point-mass expansion (a partial sum is a member of `L(G)`
  applied to `δ₁`), separation and traciality from the trace module.
* `isFactor` — over an ICC group, `L(G)` is a factor in the sense of
  `TracialStandardForm.IsFactor`.
-/

namespace GroupApproximation
namespace GroupVonNeumann

open ReducedGroupCStarTrace TwoSidedRegularCommutant TracialStandardForm
open scoped ENNReal InnerProductSpace

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

/-! ## The modular conjugation -/

theorem memℓp_conj_inv (f : GroupHilbert G) :
    Memℓp (fun x : G ↦ (starRingEnd ℂ) (f x⁻¹)) 2 := by
  apply memℓp_gen
  have h1 : Memℓp (fun x : G ↦ f x⁻¹) 2 := memℓp_comp_equiv (Equiv.inv G) f
  have hs := (memℓp_gen_iff (by norm_num)).1 h1
  simpa only [starRingEnd_apply, norm_star] using hs

/-- **The modular conjugation of the group von Neumann algebra**:
`(Jf)(x) = conj (f (x⁻¹))`. -/
def modularJ (f : GroupHilbert G) : GroupHilbert G :=
  ⟨fun x ↦ (starRingEnd ℂ) (f x⁻¹), memℓp_conj_inv G f⟩

@[simp]
theorem modularJ_apply (f : GroupHilbert G) (x : G) :
    modularJ G f x = (starRingEnd ℂ) (f x⁻¹) :=
  rfl

/-- The inner product of `δ₁` against a vector is its identity coefficient. -/
theorem inner_deltaOne_left (F : GroupHilbert G) :
    ⟪deltaOne G, F⟫_ℂ = F 1 := by
  rw [deltaOne, lp.inner_single_left, RCLike.inner_apply, map_one, one_mul]

/-- **The coefficient identity behind `J(TΩ) = T⋆Ω`**: for `T ∈ L(G)` the
adjoint's coefficient column is the conjugated, inverted column of `T`. -/
theorem star_coefficient {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ groupVonNeumannAlgebra G) (x : G) :
    (star T (deltaOne G)) x = (starRingEnd ℂ) ((T (deltaOne G)) x⁻¹) := by
  have h1 : T (lp.single 2 x 1) =
      rightRegularOperator G x (T (deltaOne G)) := by
    rw [apply_single_of_mem G hT, one_smul]
  calc (star T (deltaOne G)) x
      = ⟪(lp.single 2 x 1 : GroupHilbert G), star T (deltaOne G)⟫_ℂ := by
        rw [lp.inner_single_left, RCLike.inner_apply, map_one, one_mul]
    _ = ⟪T (lp.single 2 x 1), deltaOne G⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
    _ = (starRingEnd ℂ) ⟪deltaOne G, T (lp.single 2 x 1)⟫_ℂ := by
        rw [← inner_conj_symm]
    _ = (starRingEnd ℂ) ((T (lp.single 2 x 1)) 1) := by
        rw [inner_deltaOne_left]
    _ = (starRingEnd ℂ) ((T (deltaOne G)) x⁻¹) := by
        rw [h1, rightRegularOperator_apply, one_mul]

/-- **The modular conjugation, as the data the abstract commutation theorem
consumes.** -/
def groupTracialConjugation :
    TracialConjugation (groupVonNeumannAlgebra G) (deltaOne G) where
  J := modularJ G
  map_add := fun u v ↦ by
    apply lp.ext
    funext x
    simp only [modularJ_apply, lp.coeFn_add, Pi.add_apply, map_add]
  map_smul := fun z v ↦ by
    apply lp.ext
    funext x
    simp only [modularJ_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      map_mul]
  invol := fun v ↦ by
    apply lp.ext
    funext x
    simp only [modularJ_apply, inv_inv, Complex.conj_conj]
  inner_map := fun u v ↦ by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    calc ∑' x, ⟪modularJ G u x, modularJ G v x⟫_ℂ
        = ∑' x, ⟪v x⁻¹, u x⁻¹⟫_ℂ := tsum_congr fun x ↦ by
          rw [RCLike.inner_apply, RCLike.inner_apply, modularJ_apply,
            modularJ_apply, Complex.conj_conj, mul_comm]
      _ = ∑' x, ⟪v x, u x⟫_ℂ :=
          Equiv.tsum_eq (Equiv.inv G) fun x ↦ ⟪v x, u x⟫_ℂ
  map_orbit := fun T hT ↦ by
    apply lp.ext
    funext x
    rw [modularJ_apply, star_coefficient G hT x]

/-! ## The standard form -/

/-- **`δ₁` is a unit cyclic separating tracial vector for `L(G)`.** -/
theorem isTracialStandardForm :
    IsTracialStandardForm (groupVonNeumannAlgebra G) (deltaOne G) where
  norm_omega := norm_deltaOne G
  cyclic := by
    rw [Metric.dense_iff]
    intro f r hr
    have hsum : HasSum (fun g : G ↦ (lp.single 2 g (f g) : GroupHilbert G)) f :=
      lp.hasSum_single ENNReal.ofNat_ne_top f
    have htend : Filter.Tendsto
        (fun t : Finset G ↦ ∑ g ∈ t, (lp.single 2 g (f g) : GroupHilbert G))
        Filter.atTop (nhds f) := hsum
    obtain ⟨t, ht⟩ :=
      (htend.eventually_mem (Metric.ball_mem_nhds f hr)).exists
    have hmem : (∑ g ∈ t, f g • leftRegularOperator G g)
        ∈ groupVonNeumannAlgebra G := by
      refine sum_mem fun g _ ↦ ?_
      rw [Algebra.smul_def]
      exact mul_mem
        ((groupVonNeumannAlgebra G).toStarSubalgebra.algebraMap_mem (f g))
        (leftRegularOperator_mem G g)
    have hop : (∑ g ∈ t, f g • leftRegularOperator G g) (deltaOne G)
        = ∑ g ∈ t, (lp.single 2 g (f g) : GroupHilbert G) := by
      calc (∑ g ∈ t, f g • leftRegularOperator G g) (deltaOne G)
          = ∑ g ∈ t, (f g • leftRegularOperator G g) (deltaOne G) :=
            map_sum (ContinuousLinearMap.apply ℂ (GroupHilbert G)
              (deltaOne G)) _ t
        _ = ∑ g ∈ t, (lp.single 2 g (f g) : GroupHilbert G) :=
            Finset.sum_congr rfl fun g _ ↦ by
              rw [show (f g • leftRegularOperator G g) (deltaOne G)
                  = f g • leftRegularOperator G g (deltaOne G) from
                map_smul (ContinuousLinearMap.apply ℂ (GroupHilbert G)
                  (deltaOne G)) _ _]
              rw [leftRegularOperator_deltaOne, ← lp.single_smul]
              simp
    exact ⟨∑ g ∈ t, (lp.single 2 g (f g) : GroupHilbert G), ht,
      ⟨∑ g ∈ t, f g • leftRegularOperator G g, hmem, hop⟩⟩
  separating := fun _T hT h ↦
    eq_zero_of_mem_of_apply_deltaOne_eq_zero G hT h
  tracial := fun T hT S hS ↦ by
    rw [inner_deltaOne_left, inner_deltaOne_left]
    exact coefficient_mul_comm G hT hS

/-- **Over an ICC group, `L(G)` is a factor** in the sense of the abstract
standard-form module. -/
theorem isFactor (hG : IsICC G) :
    IsFactor (groupVonNeumannAlgebra G) := by
  intro T hTm hTc
  apply exists_smul_one_of_mem_center G hG hTm
  intro S hS
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hTc S hS).symm

end

end GroupVonNeumann
end GroupApproximation
