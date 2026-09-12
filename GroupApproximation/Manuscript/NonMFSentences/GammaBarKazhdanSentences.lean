import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.IntegralLinearResiduallyFinite
import GroupApproximation.Monsters.ExplicitIntegralLinearModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual finiteness and property (T) sentence for `Γ̄`

`non_mf_groups_exist.tex`, section "Amenable traces and Clifford lamps", right
after the display `Γ̄ = ℤ³ ⋊ SL₃(ℤ) ≤ GL₄(ℤ)` (lines 1598--1600):

> It is residually finite, since reduction modulo a suitable integer
> separates any two distinct integral matrices, and it has
> property (T) [BHV, Example 1.7.4(i)].

The sentence makes three claims.  Each one is proved, here or in a module
already on the root, with no literature input:

* the printed reason, at its printed generality: any two distinct integral
  matrices are separated by reduction modulo a nonzero integer
  (`manuscriptSentence_reductionModSuitableIntegerSeparates`; the modulus is
  `|A i j - B i j| + 1` at an entry where the two matrices differ);
* `Γ̄` is residually finite, along that route: `gammaBar` is realized by
  integral units (`ExplicitIntegralLinearModel.gammaIntEquivGammaBar`), and
  integral general linear groups are residually finite by reduction modulo an
  element-dependent modulus (`generalLinearGroup_int_residuallyFinite`);
* `Γ̄` has property (T), proved internally
  (`CommutingLampCollapse.gammaBar_hasKazhdanPropertyT`) in place of the cited
  example of Bekka--de la Harpe--Valette.

Like the census rows of the neighbouring sentences, this module takes `Γ̄` to be
the development's concrete affine base `ExplicitLinearModel.gammaBar` (row
`3229365c29c6`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace GammaBarKazhdanSentences

/-- The printed reason: reduction modulo a suitable integer separates any two
distinct integral matrices.  The modulus must be nonzero, so the reduction lands
in the finite ring `ZMod m`. -/
def PrintedReductionModSuitableIntegerSeparates : Prop :=
  ∀ (ι κ : Type) (A B : Matrix ι κ ℤ), A ≠ B →
    ∃ m : ℕ, m ≠ 0 ∧
      A.map (Int.cast : ℤ → ZMod m) ≠ B.map (Int.cast : ℤ → ZMod m)

/-- Reduction modulo `|A i j - B i j| + 1`, at an entry where `A` and `B`
differ, separates them. -/
theorem manuscriptSentence_reductionModSuitableIntegerSeparates :
    PrintedReductionModSuitableIntegerSeparates := by
  intro ι κ A B hAB
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ B i j := by
    by_contra h
    push_neg at h
    exact hAB (Matrix.ext h)
  have hz : A i j - B i j ≠ 0 := sub_ne_zero.mpr hij
  refine ⟨(A i j - B i j).natAbs + 1, Nat.succ_ne_zero _, fun heq => ?_⟩
  have h := congrFun (congrFun heq i) j
  simp only [Matrix.map_apply] at h
  exact intCast_zmod_natAbs_add_one_ne_zero hz
    (by rw [Int.cast_sub]; exact sub_eq_zero.mpr h)

/-- The printed sentence at tex lines 1598--1600: `Γ̄` is residually finite,
since reduction modulo a suitable integer separates any two distinct integral
matrices, and it has property (T). -/
def PrintedGammaBarResiduallyFiniteAndKazhdan : Prop :=
  PrintedReductionModSuitableIntegerSeparates ∧
    Group.ResiduallyFinite ExplicitLinearModel.gammaBar ∧
    HasKazhdanPropertyT.{0, 0} ExplicitLinearModel.gammaBar

/-- The sentence, with no literature input: the separation clause above,
residual finiteness through the integral realization of `Γ̄`, and property (T)
proved internally. -/
theorem manuscriptSentence_gammaBarResiduallyFiniteAndKazhdan :
    PrintedGammaBarResiduallyFiniteAndKazhdan := by
  unfold PrintedGammaBarResiduallyFiniteAndKazhdan
  exact ⟨manuscriptSentence_reductionModSuitableIntegerSeparates,
    ExplicitIntegralLinearModel.gammaBar_residuallyFinite,
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT⟩

#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.GammaBarKazhdanSentences.manuscriptSentence_reductionModSuitableIntegerSeparates
#audit_closed_axioms GroupApproximation.Manuscript.NonMFSentences.GammaBarKazhdanSentences.manuscriptSentence_gammaBarResiduallyFiniteAndKazhdan

end GammaBarKazhdanSentences
end NonMFSentences
end Manuscript
end GroupApproximation
