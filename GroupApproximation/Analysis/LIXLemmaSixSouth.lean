import GroupApproximation.Analysis.LIXLemmaSixGlue

/-!
# The southern cap as a cone on the equator

Corollary 4 glues the northern frame to a southern field built from a
null-homotopy of the stage unitary.  The southern field is defined by reading
the homotopy at the parameter `1 + Re (x 2)` and the equatorial direction of
`x`, and the direction is undefined at the south pole.  The standard cure is
to present the southern cap as a quotient of `[0,1] × S⁴` collapsing `{0} × S⁴`
to the pole, and to descend along that quotient; the homotopy is constant at
time `0`, so it descends.

This file supplies the parametrisation and its properties.  `southParam` is
the great-circle contraction of the equator to the south pole, already
available as `contractSouth` with the parameter reversed, so nothing new has
to be proved about unit vectors: `unit_contractSouth` does it.

The key computation is `re_southParam_two`: along the contraction the real
part of the third coordinate is `- sin (s π / 2)`, so the image lies in the
southern cap, it is the pole exactly at `s = 1`, and it is on the equator
exactly at `s = 0`.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-- The southern cap parametrised by the equator and a time: at `t = 1` the
equator itself, at `t = 0` the south pole. -/
def southParam (t : ℝ) (v : EuclideanSpace ℝ (Fin 5)) : Fin 3 → ℂ :=
  contractSouth e3 (1 - t) (equatorEmb v)

theorem southParam_one (v : EuclideanSpace ℝ (Fin 5)) :
    southParam 1 v = equatorEmb v := by
  rw [southParam, sub_self, contractSouth_zero]

theorem southParam_zero (v : EuclideanSpace ℝ (Fin 5)) : southParam 0 v = -e3 := by
  rw [southParam, sub_zero, contractSouth_one]

theorem unit_southParam {v : EuclideanSpace ℝ (Fin 5)} (hv : v ∈ STW59.sphereFour) (t : ℝ) :
    star (southParam t v) ⬝ᵥ southParam t v = 1 :=
  unit_contractSouth unit_e3 (isEquator_equatorEmb hv) _

theorem southParam_mem {v : EuclideanSpace ℝ (Fin 5)} (hv : v ∈ STW59.sphereFour) (t : ℝ) :
    southParam t v ∈ STW59.unitVectors (Fin 3) := by
  have h := unit_southParam hv t
  have hsum : (∑ i, ‖southParam t v i‖ ^ 2 : ℝ) = 1 := by
    have := star_dotProduct_self_ofReal (southParam t v)
    rw [h] at this
    exact_mod_cast this.symm
  exact hsum

/-- **The third coordinate along the contraction.**  Its real part is
`- sin ((1 - t) π / 2)`, which is `≤ 0` on `[0,1]`: the contraction stays in
the southern cap. -/
theorem re_southParam_two (v : EuclideanSpace ℝ (Fin 5)) (t : ℝ) :
    (southParam t v 2).re = -Real.sin ((1 - t) * (Real.pi / 2)) := by
  rw [southParam, contractSouth]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul,
    re_equatorEmb_two, mul_zero, zero_sub]
  rw [e3, Pi.single_eq_same]
  simp

theorem southParam_le_zero {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : EuclideanSpace ℝ (Fin 5)) : (southParam t v 2).re ≤ 0 := by
  rw [re_southParam_two]
  have : 0 ≤ Real.sin ((1 - t) * (Real.pi / 2)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  linarith

/-- The contraction is continuous jointly in the time and the equator point. -/
theorem continuous_southParam :
    Continuous fun q : ℝ × EuclideanSpace ℝ (Fin 5) => southParam q.1 q.2 :=
  continuous_contractSouth (continuous_const.sub continuous_fst)
    (continuous_equatorEmb.comp continuous_snd)

/-- At the pole end the parametrisation is constant in the equator variable,
which is what lets a homotopy that is trivial at time zero descend. -/
theorem southParam_zero_const (v v' : EuclideanSpace ℝ (Fin 5)) :
    southParam 0 v = southParam 0 v' := by
  rw [southParam_zero, southParam_zero]

end

end LIX
end GroupApproximation
