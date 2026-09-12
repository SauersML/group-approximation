import GroupApproximation.Higman.OmegaTowerSelectedLeadingCodeRun
import GroupApproximation.Algebra.HyperbolicFreeGroup

/-!
# Endpoint utilities for selected reduced words

This file records the sign test for a trailing row syllable, nontriviality of
the complete selected code, and the literal reduced spelling of an inverse.
The arbitrary-target factor comparison consumes these utilities without
assuming that the returning row index is already canonical.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

theorem selectedAHom_ne_one_of_toWord_ne_nil
    {m : ℕ} {B : Set E} {v : FreeGroup (SelectedBlock m B)}
    (hv : v.toWord ≠ []) : selectedAHom m B v ≠ 1 := by
  intro hcode
  have hvone : v = 1 := by
    apply selectedAHom_injective m B
    simpa using hcode
  exact hv (FreeGroup.toWord_eq_nil_iff.mpr hvone)

def selectedEndsWithRow {m : ℕ} {B : Set E}
    (p : SelectedBlock m B × Bool) : Prop :=
  p.2 = true ∧ (p.1 : E) ≠ 0

theorem toWord_inv_eq_invRev
    {A : Type} [DecidableEq A] (v : FreeGroup A) :
    v⁻¹.toWord = FreeGroup.invRev v.toWord := by
  have hred : FreeGroup.IsReduced (FreeGroup.invRev v.toWord) :=
    Hyperbolic.isReduced_invRev (FreeGroup.isReduced_toWord (x := v))
  have heq : v⁻¹ = FreeGroup.mk (FreeGroup.invRev v.toWord) := by
    rw [← FreeGroup.inv_mk, FreeGroup.mk_toWord]
  rw [heq, FreeGroup.toWord_mk]
  exact hred.reduce_eq

end Omega
end Higman
end GroupApproximation
