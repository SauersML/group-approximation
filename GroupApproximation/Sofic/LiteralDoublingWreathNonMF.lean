import GroupApproximation.Sofic.AscendingHNNSplitExtension
import GroupApproximation.Sofic.CommutingLampCollapse

/-!
# The literal doubling wreath product is not MF

**Section 39** of the dossier, assembled from the abstract endpoint.  The
concrete affine matrix group `gammaBar` has property `(T)`, and conjugation by
`diag(2,2,2,1)` is a proper injective self-embedding of it.  Feeding those two
facts to the ascending-HNN endpoint gives a completely explicit finitely
generated group that is not MF, together with the split-extension package: the
mod-two lamp base is MF, the skeleton is the MF hypothesis, and the middle
group is not MF.

Nothing here is new mathematics; it is the instantiation that makes the
abstract statement concrete, and it is the shape the manuscript's endpoint
should quote.
-/

namespace GroupApproximation
namespace LiteralDoublingWreath

open MarkedCompression ExplicitLinearModel

/-- The mod-two lamp group. -/
abbrev C2 : Type := Multiplicative (ZMod 2)

/-- The nonidentity lamp value. -/
def c : C2 := Multiplicative.ofAdd 1

theorem c_ne_one : c ≠ 1 := by
  intro h
  have : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd h
  exact one_ne_zero this

theorem c_mul_self : c * c = 1 := by
  have : Multiplicative.toAdd (c * c) = 0 := by
    show (1 : ZMod 2) + 1 = 0
    decide
  exact Multiplicative.toAdd.injective this

/-! ## Instances for the concrete base

The two countability instances this section used to carry are the ones
`ExplicitLinearModel` already provides, and this file imports it. -/

noncomputable instance cosetsDecEq :
    DecidableEq (Cosets conjD conjD_injective) := Classical.decEq _

/-- The literal doubling wreath product: mod-two lamps over the coset space of
the ascending HNN extension of the concrete affine base. -/
abbrev W : Type := WreathV (K := C2) conjD conjD_injective

/-! ## The endpoint -/

/-- **The literal doubling wreath product is not MF.**  Property `(T)` of the
affine base, properness of the doubling self-embedding, and the involutive lamp
value are the only inputs. -/
theorem not_isCDEOperatorMF_W : ¬ IsCDEOperatorMF W :=
  not_isCDEOperatorMF_wreath conjD conjD_injective
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT c_ne_one c_mul_self
    v1G_not_mem_range

theorem not_isOperatorMF_W : ¬ IsOperatorMF W := by
  intro h
  exact not_isCDEOperatorMF_W ((isCDEOperatorMF_iff_isOperatorMF _).mpr h)

/-- **The concrete split-extension package.**  The lamp base is MF, the
skeleton is MF by hypothesis, and the middle group is not MF. -/
theorem mf_fails_for_literal_split_extension
    (hV : IsOperatorMF (Vertical conjD conjD_injective)) :
    IsOperatorMF (Lamp C2 (Cosets conjD conjD_injective)) ∧
      IsOperatorMF (Vertical conjD conjD_injective) ∧
      ¬ IsOperatorMF W :=
  mf_fails_for_split_extension conjD conjD_injective
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT hV c_ne_one c_mul_self
    v1G_not_mem_range

end LiteralDoublingWreath
end GroupApproximation
