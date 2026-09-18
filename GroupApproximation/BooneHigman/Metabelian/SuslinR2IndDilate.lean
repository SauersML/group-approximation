import GroupApproximation.BooneHigman.Metabelian.SuslinR2Family
import Mathlib.Algebra.Polynomial.Inductions
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank induction for R2, part 1: dilations `X ↦ b X`

Lane `bh-met-90q`.  These are polynomial lemmas for the rank induction of
`SuslinR2BlockStatement` (`SuslinR2IndFamily.lean`).

* `suslinR2Ind_lift_poly`: **dilation lift**.  Suppose `q` over `R` has image `f(s) p`, and the
  constant term of `p` is `f(c₀)`.  Then `X q'(s X) + c₀`, with `q' = q.divX`, lifts the
  dilate `p(f(s) X)`.  No denominators survive: the factor `f(s)` of `q` is exactly
  absorbed by the dilation.
* `suslinR2Ind_mem_of_dilate`: if `b` is a unit and the dilate `σ(b X)` of a matrix is
  elementary, then so is `σ`, since `X ↦ b⁻¹ X` undoes the dilation.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

section Dilate

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `divX` commutes with coefficient maps. -/
theorem suslinR2Ind_map_divX (f : R →+* S) (q : R[X]) : q.divX.map f = (q.map f).divX := by
  ext n
  rw [coeff_map, coeff_divX, coeff_divX, coeff_map]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_map_divX

/-- **Dilation lift.**  If `q ↦ f(s) p` and `p(0) = f(c₀)`, then `X q.divX(s X) + c₀` lifts
`p(f(s) X)`. -/
theorem suslinR2Ind_lift_poly (f : R →+* S) (q : R[X]) (p : S[X]) (s c₀ : R)
    (hq : q.map f = C (f s) * p) (h0 : p.coeff 0 = f c₀) :
    (X * (q.divX.comp (C s * X)) + C c₀).map f = p.comp (C (f s) * X) := by
  have hd : q.divX.map f = C (f s) * p.divX := by
    rw [suslinR2Ind_map_divX, hq, divX_C_mul]
  conv_rhs => rw [← X_mul_divX_add p]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_comp]
  rw [hd, h0]
  simp only [add_comp, mul_comp, X_comp, C_comp]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_lift_poly

/-- Dilating by `b` and then by `c`, with `b c = 1`, is the identity. -/
theorem suslinR2Ind_comp_dilate {b c : S} (hbc : b * c = 1) (p : S[X]) :
    (p.comp (C b * X)).comp (C c * X) = p := by
  rw [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, hbc, C_1, one_mul, comp_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_comp_dilate

/-- **Undoing a dilation.**  If `b c = 1` and the dilate `σ(b X)` is elementary, then so is
`σ`. -/
theorem suslinR2Ind_mem_of_dilate {ι : Type*} [Fintype ι] [DecidableEq ι] {b c : S}
    (hbc : b * c = 1) (σ : (Matrix ι ι S[X])ˣ)
    (h : elementaryMatrixUnitMap (compRingHom (C b * X)) σ ∈ elementaryGroup ι S[X]) :
    σ ∈ elementaryGroup ι S[X] := by
  have he : elementaryMatrixUnitMap (compRingHom (C c * X))
      (elementaryMatrixUnitMap (compRingHom (C b * X)) σ) = σ := by
    apply Units.ext
    refine Matrix.ext fun i j ↦ ?_
    change (((σ : Matrix ι ι S[X]) i j).comp (C b * X)).comp (C c * X) =
      (σ : Matrix ι ι S[X]) i j
    exact suslinR2Ind_comp_dilate hbc _
  rw [← he]
  exact elementaryGroup_map_le (compRingHom (C c * X)) (Subgroup.mem_map_of_mem _ h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2Ind_mem_of_dilate

end Dilate

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
