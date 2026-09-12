import GroupApproximation.CharClass.CohomologyChartSurj
import GroupApproximation.CharClass.ProjectiveSpaceInterVanish

/-!
# Classes pulled back from the projective factor die on the intersection

The flatness step of the projective-factor Künneth.  `cc-projective`'s
`eq_zero_interSpace_even` says that **every** class of positive even degree on the
intersection of the chart cover of `ℂP^{d+1}` vanishes, because the intersection
is an odd sphere and a positive even degree is neither `0` nor `2d + 1`.  That is
stronger than the degree bound `2i ≤ 2d` I had derived from `kunneth_low`, and it
needs no relation between `i` and `d` at all.

Crossing it with `U` needs no homotopy square: the intersection of the product
cover is `Prod.snd ⁻¹'` of `cc-projective`'s intersection, so the second-projection
map to it is the pair of the second component with the membership proof the point
already carries, and a class pulled back from the projective factor restricts
through that map by `pull_comp`.

## Main results

* `KnCP.interToInterSpace` — the second projection of the intersection.
* `KnCP.pull_interToInterSpace_eq_zero` — positive even classes die.
* `KnCP.pull_cpPrCP_inter_eq_zero` — so does anything pulled back from the
  projective factor in positive even degree.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The projection of the intersection of the product cover onto `cc-projective`'s
intersection.  The membership proof is the one the point already carries, because
the product intersection is the preimage of theirs under the second projection. -/
def interToInterSpace : TopCat.of ↥(interUSet U d) ⟶ interSpace d :=
  cmap ⟨fun p => ⟨(p : U × CP (d + 1)).2, p.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

/-- **Every class of positive even degree pulled back from `cc-projective`'s
intersection vanishes.** -/
theorem pull_interToInterSpace_eq_zero (i : ℕ) (hi : i ≠ 0)
    (a : Hmod2 (interSpace d) (2 * i)) :
    pull (interToInterSpace U d) (2 * i) a = 0 := by
  rw [eq_zero_interSpace_even d i hi a, pull_zero]

/-- The projection of the whole product to the projective factor. -/
abbrev cpPrCP : cpProdTop U d ⟶ CPtop (d + 1) := cmap ContinuousMap.snd

/-- The intersection maps to the projective factor through `cc-projective`'s
intersection, on the nose. -/
theorem interToInterSpace_comp :
    interToInterSpace U d ≫ sInclusion ((chartOpen d ⊓ punctOpen d : Opens (CPtop (d + 1)))
        : Set ↥(CPtop (d + 1)))
      = sInclusion (interUSet U d) ≫ cpPrCP U d := rfl

/-- **A class pulled back from the projective factor dies on the intersection in
positive even degree.** -/
theorem pull_cpPrCP_inter_eq_zero (i : ℕ) (hi : i ≠ 0)
    (c : Hmod2 (CPtop (d + 1)) (2 * i)) :
    pull (sInclusion (interUSet U d)) (2 * i) (pull (cpPrCP U d) (2 * i) c) = 0 := by
  rw [← pull_comp, ← interToInterSpace_comp, pull_comp,
    pull_interToInterSpace_eq_zero U d i hi]

end KnCP

end

end GroupApproximation.CharClass
