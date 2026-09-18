import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Weights
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: the Mingo--Phillips operator

For a complete module `E` and a sequence `x` in `E`, `mingoPhillips hE x : H_B ⊕ E → H_B`
is the adjointable operator
`T(z, y)ₙ = 4⁻ⁿ zₙ + ⟨gen x n, y⟩`, with adjoint
`T⋆ f = (4⁻ⁿ fₙ)ₙ ⊕ ∑ₙ gen x n · fₙ`.

The series in the adjoint converges because `‖gen x n · fₙ‖ ≤ 2⁻ⁿ ‖f‖`
(`isCauchy_partialSum`), and this is where completeness of `E` is used. The adjoint
relation is a termwise identity followed by `inner_eq_tsum_of_isLimit`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule

universe v w

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {E : CStarModule.{v, w} B}

theorem norm_wt_smul_le (f : (standardModule ℕ B).carrier) (n : ℕ) :
    ‖((wt n : ℝ) : ℂ) • f.1 n‖ ≤ coef n * (standardModule ℕ B).norm f := by
  rw [norm_smul, Complex.norm_of_nonneg (wt_pos n).le]
  exact mul_le_mul (wt_le_coef n) (norm_coord_le f n) (norm_nonneg _) (coef_nonneg n)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.norm_wt_smul_le

/-- The `n`-th coordinate of `T(z, y)`. -/
noncomputable def tCoord (x : ℕ → E.carrier) (p : (prod (standardModule ℕ B) E).carrier)
    (n : ℕ) : B :=
  ((wt n : ℝ) : ℂ) • p.1.1 n + E.inner (gen x n) p.2

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.tCoord

theorem norm_tCoord_le (x : ℕ → E.carrier) (p : (prod (standardModule ℕ B) E).carrier)
    (n : ℕ) :
    ‖tCoord x p n‖ ≤ coef n * ((standardModule ℕ B).norm p.1 + E.norm p.2) := by
  have h1 := norm_wt_smul_le p.1 n
  have h2 : ‖E.inner (gen x n) p.2‖ ≤ coef n * E.norm p.2 :=
    le_trans (E.norm_inner_le _ _)
      (mul_le_mul_of_nonneg_right (norm_gen_le x n) (E.norm_nonneg _))
  calc ‖tCoord x p n‖ ≤ ‖((wt n : ℝ) : ℂ) • p.1.1 n‖ + ‖E.inner (gen x n) p.2‖ :=
        norm_add_le _ _
    _ ≤ coef n * (standardModule ℕ B).norm p.1 + coef n * E.norm p.2 := add_le_add h1 h2
    _ = coef n * ((standardModule ℕ B).norm p.1 + E.norm p.2) := (mul_add _ _ _).symm

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.norm_tCoord_le

/-- The operator `T`. -/
noncomputable def tFun (x : ℕ → E.carrier) (p : (prod (standardModule ℕ B) E).carrier) :
    (standardModule ℕ B).carrier :=
  ⟨tCoord x p, summable_of_norm_le_coef
    (add_nonneg ((standardModule ℕ B).norm_nonneg p.1) (E.norm_nonneg p.2))
    (norm_tCoord_le x p)⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.tFun

/-- The diagonal part of `T⋆`. -/
noncomputable def wtSmul (f : (standardModule ℕ B).carrier) : (standardModule ℕ B).carrier :=
  ⟨fun n => ((wt n : ℝ) : ℂ) • f.1 n,
    summable_of_norm_le_coef ((standardModule ℕ B).norm_nonneg f) (norm_wt_smul_le f)⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.wtSmul

/-- The terms of the `E`-part of `T⋆ f`. -/
noncomputable def adjSeries (x : ℕ → E.carrier) (f : (standardModule ℕ B).carrier) (n : ℕ) :
    E.carrier :=
  E.act (gen x n) (f.1 n)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.adjSeries

theorem norm_adjSeries_le (x : ℕ → E.carrier) (f : (standardModule ℕ B).carrier) (n : ℕ) :
    E.norm (adjSeries x f n) ≤ coef n * (standardModule ℕ B).norm f :=
  le_trans (E.norm_act_le _ _)
    (mul_le_mul (norm_gen_le x n) (norm_coord_le f n) (norm_nonneg _) (coef_nonneg n))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.norm_adjSeries_le

theorem adjSeries_isCauchy (x : ℕ → E.carrier) (f : (standardModule ℕ B).carrier) :
    IsCauchy E fun N => ∑ n ∈ Finset.range N, adjSeries x f n :=
  isCauchy_partialSum (adjSeries x f)
    (summable_geometric_two.mul_right ((standardModule ℕ B).norm f)) (norm_adjSeries_le x f)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.adjSeries_isCauchy

/-- The adjoint `T⋆`. -/
noncomputable def adjFun (hE : IsCompleteModule E) (x : ℕ → E.carrier)
    (f : (standardModule ℕ B).carrier) : (prod (standardModule ℕ B) E).carrier :=
  (wtSmul f, Classical.choose (hE _ (adjSeries_isCauchy x f)))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.adjFun

theorem adjFun_isLimit (hE : IsCompleteModule E) (x : ℕ → E.carrier)
    (f : (standardModule ℕ B).carrier) :
    IsLimit E (fun N => ∑ n ∈ Finset.range N, adjSeries x f n) (adjFun hE x f).2 :=
  Classical.choose_spec (hE _ (adjSeries_isCauchy x f))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.adjFun_isLimit

theorem summable_inner_adjSeries (x : ℕ → E.carrier) (y : E.carrier)
    (f : (standardModule ℕ B).carrier) :
    Summable fun n => E.inner y (adjSeries x f n) := by
  refine Summable.of_norm_bounded
    (summable_geometric_two.mul_left (E.norm y * (standardModule ℕ B).norm f)) fun n => ?_
  calc ‖E.inner y (adjSeries x f n)‖ ≤ E.norm y * E.norm (adjSeries x f n) :=
        E.norm_inner_le _ _
    _ ≤ E.norm y * (coef n * (standardModule ℕ B).norm f) :=
        mul_le_mul_of_nonneg_left (norm_adjSeries_le x f n) (E.norm_nonneg y)
    _ = E.norm y * (standardModule ℕ B).norm f * (1 / 2) ^ n := by
        rw [coef]
        ring

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.summable_inner_adjSeries

/-- **The adjoint relation for the Mingo--Phillips operator.** -/
theorem inner_tFun (hE : IsCompleteModule E) (x : ℕ → E.carrier)
    (p : (prod (standardModule ℕ B) E).carrier) (f : (standardModule ℕ B).carrier) :
    (standardModule ℕ B).inner (tFun x p) f
      = (prod (standardModule ℕ B) E).inner p (adjFun hE x f) := by
  have hterm : ∀ n, star (tCoord x p n) * f.1 n
      = star (p.1.1 n) * (wtSmul f).1 n + E.inner p.2 (adjSeries x f n) := by
    intro n
    show star (((wt n : ℝ) : ℂ) • p.1.1 n + E.inner (gen x n) p.2) * f.1 n
      = star (p.1.1 n) * (((wt n : ℝ) : ℂ) • f.1 n) + E.inner p.2 (E.act (gen x n) (f.1 n))
    rw [star_add, add_mul, star_smul, star_ofReal_complex, smul_mul_assoc, ← mul_smul_comm,
      E.inner_star, E.inner_act_right]
  show ∑' n, star (tCoord x p n) * f.1 n
    = ∑' n, star (p.1.1 n) * (wtSmul f).1 n + E.inner p.2 (adjFun hE x f).2
  rw [tsum_congr hterm,
    (summable_star_mul (summable_coe p.1) (summable_coe (wtSmul f))).tsum_add
      (summable_inner_adjSeries x p.2 f),
    ← inner_eq_tsum_of_isLimit (adjFun_isLimit hE x f) p.2 (summable_inner_adjSeries x p.2 f)]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.inner_tFun

/-- **The Mingo--Phillips operator** `H_B ⊕ E → H_B`. -/
noncomputable def mingoPhillips (hE : IsCompleteModule E) (x : ℕ → E.carrier) :
    Adjointable (prod (standardModule ℕ B) E) (standardModule ℕ B) where
  toFun := tFun x
  adj := adjFun hE x
  inner_adj := inner_tFun hE x

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.mingoPhillips

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
