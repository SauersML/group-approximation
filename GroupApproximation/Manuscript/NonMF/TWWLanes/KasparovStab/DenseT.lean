import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.DenseAdj
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: the operator has dense range

`T = mingoPhillips hE x` has dense range, for any sequence `x`. Its restriction to
`H_B ⊕ 0` is the diagonal operator `diag(4⁻ⁿ)`. Every truncation `truncate s f` is
`T (invTrunc s f, 0)`, where `invTrunc s f` rescales the finitely many coordinates in `s`
by `4ⁿ`. Truncations are dense by `exists_truncate_norm_le`.
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

/-- The truncation of `f` to `s`, with coordinate `n` rescaled by `(4⁻ⁿ)⁻¹`. -/
noncomputable def invTrunc (s : Finset ℕ) (f : (standardModule ℕ B).carrier) :
    (standardModule ℕ B).carrier :=
  ⟨fun n => if n ∈ s then (((wt n)⁻¹ : ℝ) : ℂ) • f.1 n else 0, by
    show Summable fun i => star (if i ∈ s then (((wt i)⁻¹ : ℝ) : ℂ) • f.1 i else 0)
      * (if i ∈ s then (((wt i)⁻¹ : ℝ) : ℂ) • f.1 i else 0)
    refine summable_of_ne_finset_zero (s := s) fun i hi => ?_
    simp [hi]⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.invTrunc

theorem invTrunc_coe (s : Finset ℕ) (f : (standardModule ℕ B).carrier) (n : ℕ) :
    (invTrunc s f).1 n = if n ∈ s then (((wt n)⁻¹ : ℝ) : ℂ) • f.1 n else 0 := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.invTrunc_coe

/-- **`T (invTrunc s f, 0) = truncate s f`.** -/
theorem tFun_invTrunc (hE : IsCompleteModule E) (x : ℕ → E.carrier) (s : Finset ℕ)
    (f : (standardModule ℕ B).carrier) :
    (mingoPhillips hE x).toFun
        ((invTrunc s f, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier)
      = truncate s f := by
  refine Subtype.ext (funext fun n => ?_)
  show ((wt n : ℝ) : ℂ) • (invTrunc s f).1 n + E.inner (gen x n) (0 : E.carrier)
    = (truncate s f).1 n
  rw [E.inner_zero_right, add_zero, invTrunc_coe]
  by_cases hn : n ∈ s
  · rw [truncate_coe_of_mem hn, if_pos hn, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (wt_pos n).ne', Complex.ofReal_one, one_smul]
  · rw [truncate_coe_of_not_mem hn, if_neg hn, smul_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.tFun_invTrunc

/-- **The Mingo--Phillips operator has dense range.** -/
theorem hasDenseRange_mingoPhillips (hE : IsCompleteModule E) (x : ℕ → E.carrier) :
    HasDenseRange (mingoPhillips hE x) := by
  intro f ε hε
  obtain ⟨s, hs⟩ := exists_truncate_norm_le f hε
  refine ⟨((invTrunc s f, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier), ?_⟩
  rw [tFun_invTrunc hE x s f]
  exact (modNorm_sub_comm (standardModule ℕ B) (truncate s f) f).trans_le hs

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.hasDenseRange_mingoPhillips

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
